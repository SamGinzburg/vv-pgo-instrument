use std::collections::HashMap;
use std::collections::HashSet;
use crate::MapValue;
use walrus::*;
use walrus::ir::*;
use crate::Profile;

pub fn generate_stubs(module: &mut Module,
                  final_types: &mut HashSet<(TypeId, TableId)>,
                  stubs: &mut HashMap<TypeId, FunctionId>,
                  modified_map: &mut HashMap<usize, MapValue>,
                  map: &Option<Profile>,
                  is_opt: bool) {

    let mut idx = 0;
    if !is_opt {
        for (ty, tab) in final_types.clone() {
            // Look up parameters / results from the type id
            let mut params = Vec::from(module.types.get(ty).params());
            let old_params = params.clone();
            // call target location (for profiling)
            params.push(ValType::I32);
            // call_indirect target value
            params.push(ValType::I32);

            let results = Vec::from(module.types.get(ty).results());
            let mut indirect_stub = FunctionBuilder::new(&mut module.types, &params, &results);
            indirect_stub.name(format!("indirect_stub_{}", idx));
            idx += 1;
            let mut param_locals = vec![];

            // push one extra local for tracking call sites when profiling
            param_locals.push(module.locals.add(ValType::I32));

            for p in &params {
                let n = module.locals.add(*p);
                param_locals.push(n);
            }

            let mut func_body = indirect_stub.func_body();

            for idx in 0..(params.len() - 1) {
                func_body.local_get(param_locals[idx]);
            }

            // Find the *correct* type for the indirect call
            let new_ty = module.types.find(&old_params, &results).unwrap();
            assert!(new_ty == ty, "type mismatch when creating stubs");
            func_body.call_indirect(ty, tab);

            let indirect_stub_id = indirect_stub.finish(param_locals, &mut module.funcs);
            stubs.insert(ty, indirect_stub_id);
        }
    } else {
        // When optimizing we still need to construct new functions!
        // For each indirect call we are directizing, we create a stub that takes in an
        // extra i32 param, to avoid dealing with extra
        for (key, val) in &modified_map.clone() {
            match val.f_id {
                Some(id) => {
                    // If we have some function, we want to make a function that calls it for us!
                    // First get the types of the old function
                    println!(
                        "Optimizing function: {}",
                        &module.funcs.get(id).name.as_ref().unwrap()
                    );
                    let ty_id = module.funcs.get(id).ty();
                    let mut params = Vec::from(module.types.get(ty_id).params());
                    let old_params = params.clone();
                    // call target location (to trap if we messed up & maintain the same params)
                    params.push(ValType::I32);

                    let results = Vec::from(module.types.get(ty_id).results());

                    let mut temp = FunctionBuilder::new(&mut module.types, &params, &results);
                    temp.name(format!("indirect_call_stub_{}", idx));
                    idx += 1;
                    let mut param_locals = vec![];

                    for p in &params {
                        let n = module.locals.add(*p);
                        param_locals.push(n);
                    }
                    let mut func_body = temp.func_body();

                    // Check that the call target matches
                    let target = *map.as_ref().unwrap().map.get(key).unwrap();
                    func_body.block_at(0, None, |block| {
                        block
                            .i32_const(target)
                            .local_get(param_locals[params.len() - 1])
                            .binop(BinaryOp::I32Ne)
                            .if_else(
                                None,
                                |then| {
                                    then.unreachable();
                                },
                                |_| {},
                            );
                    });

                    for idx in 0..(params.len() - 1) {
                        func_body.local_get(param_locals[idx]);
                    }

                    // call the old id!
                    func_body.call(id);

                    let new_id = temp.finish(param_locals, &mut module.funcs);

                    let val = MapValue {
                        f_id: Some(new_id),
                        f_bool: false,
                    };
                    modified_map.insert(*key, val);

                    let new_ty = module.types.find(&old_params, &results).unwrap();
                    assert!(new_ty == ty_id, "type mismatch when creating stubs");
                }
                _ => (),
            }
        }
    }
}



