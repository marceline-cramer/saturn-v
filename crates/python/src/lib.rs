use std::ops::Deref;

use pyo3::{
    exceptions::{PyRuntimeError, PyValueError},
    prelude::*,
    types::PyString,
};
use saturn_v_client::Client;
use saturn_v_protocol::{Program, RelationInfo};

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

    pub async fn get_inputs(&self) -> PyResult<String> {
        let inputs = self
            .inner
            .get_inputs()
            .await
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;
        let infos: Vec<RelationInfo> = inputs.iter().map(|i| i.deref().clone()).collect();
        serde_json::to_string(&infos).map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    pub async fn get_input(&self, name: String) -> PyResult<String> {
        let input = self
            .inner
            .get_input(&name)
            .await
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;

        let info = input.deref().clone();

        serde_json::to_string(&info).map_err(|e| PyRuntimeError::new_err(e.to_string()))
    }

    pub async fn get_outputs(&self) -> PyResult<String> {
        let outputs = self
            .inner
            .get_outputs()
            .await
            .map_err(|e| PyRuntimeError::new_err(e.to_string()))?;

        let infos: Vec<RelationInfo> = outputs.iter().map(|o| o.deref().clone()).collect();

        serde_json::to_string(&infos).map_err(|e| PyRuntimeError::new_err(e.to_string()))
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

#[pymodule]
fn saturn_v_py(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyClient>()?;
    Ok(())
}
