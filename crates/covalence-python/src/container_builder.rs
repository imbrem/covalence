use std::sync::{Arc, Mutex};

use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

use crate::component_builder::ComponentBuilder;
use crate::container::Container;
use crate::module_builder::ModuleBuilder;
use crate::system_builder::{
    ComponentData, ComponentId, ContainerData, ContainerId, SystemBuilder,
    extract_hash_for_container,
};

#[pyclass]
pub struct ContainerBuilder {
    pub(crate) system: Arc<Mutex<SystemBuilder>>,
    pub(crate) id: ContainerId,
}

#[pymethods]
impl ContainerBuilder {
    #[new]
    fn new() -> Self {
        let mut sys = SystemBuilder::new();
        let container_id = sys.containers.insert(ContainerData {
            component: None,
            link_hash: None,
            instance_imports: Vec::new(),
            has_attest: false,
            built_hash: None,
        });
        let component_id = sys.components.insert(ComponentData {
            container: Some(container_id),
            module: None,
        });
        sys.containers[container_id].component = Some(component_id);
        ContainerBuilder {
            system: Arc::new(Mutex::new(sys)),
            id: container_id,
        }
    }

    #[staticmethod]
    fn from_link(hash: &Bound<'_, PyAny>) -> PyResult<Self> {
        let h = extract_hash_for_container(hash)?;
        let mut sys = SystemBuilder::new();
        let container_id = sys.containers.insert(ContainerData {
            component: None,
            link_hash: Some(h),
            instance_imports: Vec::new(),
            has_attest: false,
            built_hash: Some(h),
        });
        Ok(ContainerBuilder {
            system: Arc::new(Mutex::new(sys)),
            id: container_id,
        })
    }

    #[getter]
    fn component(&self) -> PyResult<ComponentBuilder> {
        let sys = self.system.lock().unwrap();
        let comp_id = Self::require_component_id(&sys, self.id)?;
        Ok(ComponentBuilder {
            system: Arc::clone(&self.system),
            id: comp_id,
        })
    }

    fn module(&self) -> PyResult<ModuleBuilder> {
        let mut sys = self.system.lock().unwrap();
        let comp_id = Self::require_component_id(&sys, self.id)?;

        if let Some(module_id) = sys.components[comp_id].module {
            return Ok(ModuleBuilder {
                system: Arc::clone(&self.system),
                id: module_id,
            });
        }

        let module_id = sys
            .modules
            .insert(SystemBuilder::new_module_data(Some(comp_id)));
        sys.components[comp_id].module = Some(module_id);

        Ok(ModuleBuilder {
            system: Arc::clone(&self.system),
            id: module_id,
        })
    }

    #[getter]
    fn wat(&self) -> PyResult<String> {
        let sys = self.system.lock().unwrap();
        sys.generate_container_wat(self.id)
    }

    fn build(&self) -> PyResult<Container> {
        let wat = {
            let sys = self.system.lock().unwrap();
            sys.generate_container_wat(self.id)?
        };
        let container = Container::from_wat(&wat)?;
        {
            let mut sys = self.system.lock().unwrap();
            sys.containers[self.id].built_hash = Some(container.content_hash());
        }
        Ok(container)
    }
}

impl ContainerBuilder {
    fn require_component_id(sys: &SystemBuilder, id: ContainerId) -> PyResult<ComponentId> {
        sys.containers[id]
            .component
            .ok_or_else(|| PyValueError::new_err("link-mode ContainerBuilder has no component"))
    }
}
