use std::sync::{Arc, Mutex};

use pyo3::prelude::*;

use crate::component::Component;
use crate::container_builder::ContainerBuilder;
use crate::module_builder::ModuleBuilder;
use crate::system_builder::{ComponentData, ComponentId, ModuleData, SystemBuilder};

#[pyclass]
pub struct ComponentBuilder {
    pub(crate) system: Arc<Mutex<SystemBuilder>>,
    pub(crate) id: ComponentId,
}

#[pymethods]
impl ComponentBuilder {
    #[new]
    #[pyo3(signature = (container=None))]
    pub fn new(container: Option<&ContainerBuilder>) -> PyResult<Self> {
        match container {
            Some(cb) => {
                let mut sys = cb.system.lock().unwrap();
                let comp_id = sys.components.insert(ComponentData {
                    container: Some(cb.id),
                    module: None,
                });
                sys.containers[cb.id].component = Some(comp_id);
                Ok(ComponentBuilder {
                    system: Arc::clone(&cb.system),
                    id: comp_id,
                })
            }
            None => {
                let mut sys = SystemBuilder::new();
                let comp_id = sys.components.insert(ComponentData {
                    container: None,
                    module: None,
                });
                Ok(ComponentBuilder {
                    system: Arc::new(Mutex::new(sys)),
                    id: comp_id,
                })
            }
        }
    }

    #[getter]
    fn container(&self) -> Option<ContainerBuilder> {
        let sys = self.system.lock().unwrap();
        let container_id = sys.components[self.id].container?;
        Some(ContainerBuilder {
            system: Arc::clone(&self.system),
            id: container_id,
        })
    }

    fn module(&self) -> ModuleBuilder {
        let mut sys = self.system.lock().unwrap();
        if let Some(module_id) = sys.components[self.id].module {
            return ModuleBuilder {
                system: Arc::clone(&self.system),
                id: module_id,
            };
        }

        let module_id = sys.modules.insert(ModuleData {
            component: Some(self.id),
            imports: Vec::new(),
            funcs: Vec::new(),
            exports: Vec::new(),
            start_calls: Vec::new(),
            explicit_start: None,
        });
        sys.components[self.id].module = Some(module_id);

        ModuleBuilder {
            system: Arc::clone(&self.system),
            id: module_id,
        }
    }

    #[getter]
    fn wat(&self) -> String {
        let sys = self.system.lock().unwrap();
        match sys.components[self.id].module {
            Some(mid) => sys.generate_module_wat(mid),
            None => "(module)".to_string(),
        }
    }

    fn build(&self) -> PyResult<Component> {
        let wat = {
            let sys = self.system.lock().unwrap();
            sys.build_component_wat(self.id)
        };
        Component::from_wat(&wat)
    }
}
