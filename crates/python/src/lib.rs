use ordered_float::OrderedFloat;
use pyo3::{
    exceptions::{PyRuntimeError, PyValueError},
    prelude::*,
    types::{PyBool, PyFloat, PyInt, PyString, PyTuple},
};
use saturn_v_client::{Client, Error, Input, Output};
use saturn_v_protocol::{Program, StructuredValue};

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

    pub async fn get_program(&self) -> PyResult<String> {
        let prog = self.inner.get_program().await.map_err(err_to_py)?;

        serde_json::to_string(&prog).map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    pub async fn set_program(&self, program: String) -> PyResult<()> {
        let prog: Program =
            serde_json::from_str(&program).map_err(|e| PyValueError::new_err(e.to_string()))?;

        self.inner.set_program(&prog).await.map_err(err_to_py)?;

        Ok(())
    }

    pub async fn get_inputs(&self) -> PyResult<Vec<PyInput>> {
        let inputs = self.inner.get_inputs().await.map_err(err_to_py)?;

        Ok(inputs.into_iter().map(|i| PyInput { inner: i }).collect())
    }

    pub async fn get_input(&self, name: String) -> PyResult<PyInput> {
        self.inner
            .get_input(&name)
            .await
            .map(|inner| PyInput { inner })
            .map_err(err_to_py)
    }

    pub async fn get_outputs(&self) -> PyResult<Vec<PyOutput>> {
        let outputs = self.inner.get_outputs().await.map_err(err_to_py)?;

        Ok(outputs
            .into_iter()
            .map(|inner| PyOutput { inner })
            .collect())
    }

    pub async fn get_output(&self, name: String) -> PyResult<PyOutput> {
        self.inner
            .get_output(&name)
            .await
            .map(|inner| PyOutput { inner })
            .map_err(err_to_py)
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

    pub async fn insert(&self, value: Py<PyAny>) -> PyResult<()> {
        let value = Python::attach(move |py| py_to_satv(value.into_bound(py)))?;

        self.inner.update_raw(value, true).await.map_err(err_to_py)
    }

    pub async fn remove(&self, value: Py<PyAny>) -> PyResult<()> {
        let value = Python::attach(move |py| py_to_satv(value.into_bound(py)))?;

        self.inner.update_raw(value, false).await.map_err(err_to_py)
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

    pub async fn get_all(&self) -> PyResult<Vec<Py<PyAny>>> {
        let raw = self.inner.get_all_raw().await.map_err(err_to_py)?;

        Python::try_attach(move |py| {
            raw.into_iter()
                .flat_map(|val| satv_to_py(val, py))
                .collect()
        })
        .ok_or_else(|| PyRuntimeError::new_err("failed to attach to interpreter"))
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
    PyRuntimeError::new_err(format!("{err:#?}"))
}
