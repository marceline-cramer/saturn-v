use ordered_float::OrderedFloat;
use pyo3::{
    exceptions::{PyRuntimeError, PyValueError},
    prelude::*,
    types::{PyBool, PyFloat, PyInt, PyString, PyTuple},
};
use pyo3_async_runtimes::tokio::future_into_py;
use saturn_v_client::{Client, Error, Input, Output, QueryRelation};
use saturn_v_protocol::StructuredValue;

#[pyclass]
#[derive(Clone)]
pub struct PyClient {
    inner: Client,
}

#[pymethods]
impl PyClient {
    #[new]
    pub fn new(base: Bound<'_, PyString>) -> PyResult<Self> {
        let url = base
            .to_str()?
            .parse()
            .map_err(|e| PyValueError::new_err(format!("invalid URL: {e}")))?;

        Ok(PyClient {
            inner: Client::new(url),
        })
    }

    pub fn get_program<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let client = self.inner.clone();
        future_into_py(py, async move {
            let prog = client.get_program().await.map_err(err_to_py)?;
            serde_json::to_string_pretty(&prog).map_err(|e| PyRuntimeError::new_err(e.to_string()))
        })
    }

    pub fn set_program<'py>(
        &self,
        py: Python<'py>,
        program: String,
    ) -> PyResult<Bound<'py, PyAny>> {
        let client = self.inner.clone();
        future_into_py(py, async move {
            let prog =
                serde_json::from_str(&program).map_err(|e| PyValueError::new_err(e.to_string()))?;
            client.set_program(&prog).await.map_err(err_to_py)?;
            Ok(())
        })
    }

    pub fn get_inputs<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let client = self.inner.clone();
        future_into_py(py, async move {
            Ok(client
                .get_inputs()
                .await
                .map_err(err_to_py)?
                .into_iter()
                .map(|i| PyInput { inner: i })
                .collect::<Vec<_>>())
        })
    }

    pub fn get_input<'py>(&self, py: Python<'py>, name: String) -> PyResult<Bound<'py, PyAny>> {
        let client = self.inner.clone();
        future_into_py(py, async move {
            client
                .get_input(&name)
                .await
                .map(|inner| PyInput { inner })
                .map_err(err_to_py)
        })
    }

    pub fn get_outputs<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        let client = self.inner.clone();
        future_into_py(py, async move {
            Ok(client
                .get_outputs()
                .await
                .map_err(err_to_py)?
                .into_iter()
                .map(|inner| PyOutput { inner })
                .collect::<Vec<_>>())
        })
    }

    pub fn get_output<'py>(&self, py: Python<'py>, name: String) -> PyResult<Bound<'py, PyAny>> {
        let client = self.inner.clone();
        future_into_py(py, async move {
            client
                .get_output(&name)
                .await
                .map(|inner| PyOutput { inner })
                .map_err(err_to_py)
        })
    }
}

#[pyclass]
#[derive(Clone)]
pub struct PyInput {
    inner: Input,
}

#[pymethods]
impl PyInput {
    #[getter]
    pub fn name(&self) -> String {
        self.inner.name.clone()
    }

    #[getter]
    pub fn id(&self) -> String {
        self.inner.id.clone()
    }

    pub fn insert<'py>(&self, value: Bound<'py, PyAny>) -> PyResult<Bound<'py, PyAny>> {
        let py = value.py();
        let input = self.inner.clone();
        let value = py_to_satv(value)?;
        future_into_py(py, async move {
            input.update(value, true).await.map_err(err_to_py)?;
            Ok(())
        })
    }

    pub fn remove<'py>(&self, value: Bound<'py, PyAny>) -> PyResult<Bound<'py, PyAny>> {
        let py = value.py();
        let input = self.inner.clone();
        let value = py_to_satv(value)?;
        future_into_py(py, async move {
            input.update(value, true).await.map_err(err_to_py)?;
            Ok(())
        })
    }

    pub fn get_all<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        get_all(self.inner.clone(), py)
    }
}

#[pyclass]
#[derive(Clone)]
pub struct PyOutput {
    inner: Output,
}

#[pymethods]
impl PyOutput {
    #[getter]
    pub fn name(&self) -> String {
        self.inner.name.clone()
    }

    #[getter]
    pub fn id(&self) -> String {
        self.inner.id.clone()
    }

    pub fn get_all<'py>(&self, py: Python<'py>) -> PyResult<Bound<'py, PyAny>> {
        get_all(self.inner.clone(), py)
    }
}

#[pymodule]
fn saturn_v_py(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyClient>()?;
    m.add_class::<PyInput>()?;
    m.add_class::<PyOutput>()?;
    Ok(())
}

pub fn satv_to_py<'py>(v: StructuredValue, py: Python<'py>) -> PyResult<Py<PyAny>> {
    use StructuredValue::*;
    Ok(match v {
        Tuple(els) => {
            let items = els
                .into_iter()
                .map(|e| satv_to_py(e, py))
                .collect::<PyResult<Vec<_>>>()?;

            PyTuple::new(py, items)?.into_any()
        }
        String(s) | Symbol(s) => PyString::intern(py, &s).into_any(),
        Integer(i) => PyInt::new(py, i).into_any(),
        Real(f) => PyFloat::new(py, f.into_inner()).into_any(),
        Boolean(b) => PyBool::new(py, b).as_any().to_owned(),
    }
    .as_unbound()
    .clone_ref(py))
}

pub fn py_to_satv<'py>(val: Bound<'py, PyAny>) -> PyResult<StructuredValue> {
    if let Ok(tuple) = val.extract::<Vec<_>>() {
        tuple
            .into_iter()
            .map(py_to_satv)
            .collect::<PyResult<Vec<_>>>()
            .map(StructuredValue::Tuple)
    } else if let Ok(float) = val.extract() {
        Ok(StructuredValue::Real(OrderedFloat(float)))
    } else if let Ok(bool) = val.extract() {
        Ok(StructuredValue::Boolean(bool))
    } else if let Ok(string) = val.extract() {
        Ok(StructuredValue::String(string))
    } else if let Ok(int) = val.extract() {
        Ok(StructuredValue::Integer(int))
    } else {
        Err(PyRuntimeError::new_err("cannot extract Saturn V value"))
    }
}

pub fn err_to_py(err: Error) -> PyErr {
    PyRuntimeError::new_err(err.to_string())
}

pub fn get_all<'py, T: QueryRelation + Send + 'static>(
    relation: T,
    py: Python<'py>,
) -> PyResult<Bound<'py, PyAny>> {
    future_into_py(py, async move {
        let raw = relation.get_all().await.map_err(err_to_py)?;

        Python::try_attach(move |py| {
            raw.into_iter()
                .flat_map(|val| satv_to_py(val, py))
                .collect::<Vec<_>>()
        })
        .ok_or_else(|| PyRuntimeError::new_err("failed to attach to interpreter"))
    })
}
