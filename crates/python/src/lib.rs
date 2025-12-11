use std::ops::Deref;

use pyo3::{
    exceptions::{PyRuntimeError, PyValueError},
    prelude::*,
    types::PyString,
};
use saturn_v_client::{Client, Input, Output};
use saturn_v_protocol::Program;

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
        let prog = self
            .inner
            .get_program()
            .await
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;

        serde_json::to_string(&prog).map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    pub async fn set_program(&self, program: String) -> PyResult<()> {
        let prog: Program =
            serde_json::from_str(&program).map_err(|e| PyValueError::new_err(e.to_string()))?;

        self.inner
            .set_program(&prog)
            .await
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;

        Ok(())
    }

    pub async fn get_inputs(&self) -> PyResult<Vec<PyInput>> {
        let inputs = self
            .inner
            .get_inputs()
            .await
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
        Ok(inputs.into_iter().map(|i| PyInput { inner: i }).collect())
    }

    pub async fn get_input(&self, name: String) -> PyResult<PyInput> {
        self.inner
            .get_input(&name)
            .await
            .map(|inner| PyInput { inner })
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    pub async fn get_outputs(&self) -> PyResult<Vec<PyOutput>> {
        let outputs = self
            .inner
            .get_outputs()
            .await
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;

        Ok(outputs
            .into_iter()
            .map(|inner| PyOutput { inner })
            .collect())
    }

    pub async fn get_output(&self, name: String) -> PyResult<String> {
        let output = self
            .inner
            .get_output(&name)
            .await
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;

        let info = output.deref().clone();

        serde_json::to_string(&info).map_err(|e| PyRuntimeError::new_err(e.to_string()))
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

    pub async fn insert(&self, value: String) -> PyResult<()> {
        self.inner
            .insert(&value)
            .await
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    pub async fn remove(&self, value: String) -> PyResult<()> {
        self.inner
            .remove(&value)
            .await
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))
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
        let vals = self
            .inner
            .get_all_raw()
            .await
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;

        todo!()
    }
}

#[pymodule]
fn saturn_v_py(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyClient>()?;
    m.add_class::<PyInput>()?;
    m.add_class::<PyOutput>()?;
    Ok(())
}
