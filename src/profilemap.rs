use walrus::*;
use walrus::InitExpr::*;
use walrus::ir::Value;
use std::collections::HashMap;
use crate::Profile;

// In our modified map, we can perform 3 operations:
// 1) Replace an indirect call with a func id
// 2) Replace an indirect call with "unreachable"
// 3) No-op
#[derive(Clone, Debug)]
pub struct MapValue {
    pub f_id: Option<Vec<FunctionId>>,
    pub f_bool: bool,
}

pub fn process_map(module: &Module, original_map: &Option<Profile>, modified_map: &mut HashMap<usize, MapValue>) -> () {
    let tab_id = module.tables.main_function_table().unwrap().unwrap();
    let table = module.tables.get(tab_id);
    for elem in &table.elem_segments {
        let e = module.elements.get(*elem);
        let offset: usize = match e.kind {
            walrus::ElementKind::Active {
                table: t,
                offset: expr,
            } => match expr {
                walrus::InitExpr::Value(Value::I32(x)) => x as usize,
                _ => 0,
            },
            _ => 0,
        };

        //dbg!(&e.members);

        // Now that we have the offset, we can remap our profile data
        // We recorded a mapping of indicies in this table to a value of {-1/-2/integer >= 0}
        // We need to remap the index in this table to a FuncionId in this element
        // Later we will replace indirect calls using this mapping of global idx ==> FunctionId
        for (global_idx, indirect_idx) in &original_map.as_ref().unwrap().map {
            // Vec contains actual func calls
            let calls: Vec<&i32> = indirect_idx.iter().filter(|val| **val != -2 && **val != -1).collect::<Vec<&i32>>();
            if calls.len() > 0 {
                //dbg!(&calls);
                let mut func_ids = vec![];
                for id in calls {
                    func_ids.push(e.members[(*id as usize) - offset].unwrap());
                }
                let val = MapValue {
                    f_id: Some(func_ids),
                    f_bool: false,
                };
                modified_map.insert(*global_idx, val);
            // if we must retain the indirect call
            // if the values have been set to -2
            } else if indirect_idx.iter().filter(|val| **val == -2).collect::<Vec<&i32>>().len() == indirect_idx.len() {
                //dbg!(&indirect_idx.iter().filter(|val| **val == -2).collect::<Vec<&i32>>());
                let val = MapValue {
                    f_id: None,
                    f_bool: false,
                };
                modified_map.insert(*global_idx, val);
            } else {
                let val = MapValue {
                    f_id: None,
                    f_bool: true,
                };
                modified_map.insert(*global_idx, val);
            }
        }
        break;
    }
}
