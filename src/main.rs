use clap::{value_t, App, Arg};
use rmp_serde::decode;
use serde::Deserialize;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fs::File;
use std::io::Read;
use walrus::ir::Instr::*;
use walrus::ir::Value;
use walrus::ir::VisitorMut;
use walrus::ir::*;
use walrus::DataKind::Active;
use walrus::FunctionBuilder;
use walrus::FunctionId;
use walrus::GlobalId;
use walrus::InstrSeqBuilder;
use walrus::TableId;
use walrus::TypeId;
use walrus::ValType;

#[derive(Deserialize, Debug)]
struct Profile {
    map: HashMap<usize, i32>,
}

#[derive(Debug)]
struct TypeScan {
    ty: Vec<(TypeId, TableId)>,
}

// In our modified map, we can perform 3 operations:
// 1) Replace an indirect call with a func id
// 2) Replace an indirect call with "unreachable"
// 3) No-op
#[derive(Clone, Debug)]
struct MapValue {
    f_id: Option<FunctionId>,
    f_bool: bool,
}

impl VisitorMut for TypeScan {
    fn visit_instr_mut(&mut self, instr: &mut walrus::ir::Instr, idx: &mut walrus::InstrLocId) {
        match instr {
            CallIndirect(call_indirect) => {
                self.ty.push((call_indirect.ty, call_indirect.table));
            }
            _ => {}
        }
    }
}

fn main() {
    let matches = App::new("vectorvisor")
        .version("0.1")
        .author("Sam Ginzburg <ginzburg.sam@gmail.com>")
        .about("A WASM profiling utility for VectorVisor")
        .arg(
            Arg::with_name("input")
                .required(true)
                .short("i")
                .long("input")
                .value_name("")
                .help("The input .wasm binary to instrument/optimize")
                .multiple(false)
                .number_of_values(1)
                .takes_value(true),
        )
        .arg(
            Arg::with_name("output")
                .required(true)
                .short("o")
                .long("output")
                .value_name("")
                .help("The output {instrumented/optimized} .wasm binary")
                .multiple(false)
                .number_of_values(1)
                .takes_value(true),
        )
        .arg(
            Arg::with_name("optimize")
                .short("prof")
                .long("profile")
                .help("Emit an optimized binary using then given profiling data")
                .multiple(false)
                .number_of_values(1)
                .takes_value(true),
        )
        .get_matches();

    let input = value_t!(matches.value_of("input"), String).unwrap_or_else(|e| e.exit());
    let output = value_t!(matches.value_of("output"), String).unwrap_or_else(|e| e.exit());
    let optimize: Option<&str> = matches.value_of("optimize");
    let is_opt = match optimize {
        Some(_) => true,
        _ => false,
    };
    let map: Option<Profile> = match optimize {
        Some(path) => {
            let mut file = File::open(path).unwrap();
            let mut buf = vec![];
            file.read_to_end(&mut buf);
            decode::from_read(&buf as &[u8]).unwrap()
        }
        _ => None,
    };

    let mut module = walrus::Module::from_file(input).unwrap();

    // We need to map the profiling data to FunctionId refs in the AST
    // We parse table 0, get the offset, and then iterate through the functions
    let mut modified_map: HashMap<usize, MapValue> = HashMap::new();
    let tab_id = module.tables.main_function_table().unwrap().unwrap();
    let table = module.tables.get(tab_id);
    if is_opt {
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
            for (global_idx, indirect_idx) in &map.as_ref().unwrap().map {
                if *indirect_idx >= 0 {
                    /*
                    let val = MapValue {
                        f_id: e.members[0],
                        f_bool: false,
                    };
                    */
                    let val = MapValue {
                        f_id: e.members[(*indirect_idx as usize) - offset],
                        f_bool: false,
                    };
                    modified_map.insert(*global_idx, val);
                // if we must retain the indirect call
                } else if *indirect_idx == -2 {
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

    let original_map = modified_map.clone();
    // Scan for all indirect call types
    let types: Vec<Vec<(TypeId, TableId)>> = module
        .funcs
        .iter_local_mut()
        .map(|(id, func)| {
            let entry = func.entry_block();
            let mut scan = TypeScan { ty: vec![] };
            walrus::ir::dfs_pre_order_mut(&mut scan, func, entry);

            scan.ty
        })
        .collect();

    let mut final_types: HashSet<(TypeId, TableId)> = HashSet::new();
    for ty in types {
        final_types.extend(ty);
    }

    // For each indirect call type generate a new function in the module to serve as a stub
    let mut stubs: HashMap<TypeId, FunctionId> = HashMap::new();
    let mut idx = 0;
    if !is_opt {
        for (ty, tab) in final_types {
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

    // values
    let mut skip_funcs: HashSet<FunctionId> = HashSet::new();
    for id in stubs.values() {
        skip_funcs.insert(*id);
    }

    // Track each indirect call we replace
    // We want to know which calls we can replace with direct calls after profiling
    let mut global_index = 0;

    module.funcs.iter_local_mut().for_each(|(id, func)| {
        // Skip the stubs we created...
        if !skip_funcs.contains(&id) {
            let mut body = func.entry_block();
            let mut count: usize = 0;
            let mut insertion_point: Vec<(InstrSeqId, usize, TypeId)> = vec![];
            let mut seqs_to_process: Vec<InstrSeqId> = vec![];
            seqs_to_process.push(body);
            drop(body);

            while seqs_to_process.len() > 0 {
                let current_seq = seqs_to_process.pop().unwrap();
                let bmut = func.block_mut(current_seq);
                let mut offset = 0;
                for (instr, loc) in &bmut.instrs {
                    match instr {
                        CallIndirect(call) => {
                            insertion_point.push((current_seq.clone(), count + offset, call.ty));
                            if !is_opt {
                                offset += 1;
                            }
                        }
                        Block(b) => {
                            seqs_to_process.push(b.seq);
                        }
                        Loop(l) => {
                            seqs_to_process.push(l.seq);
                        }
                        _ => {}
                    }
                    count += 1;
                }
                count = 0;
            }
            drop(body);

            if !is_opt {
                // Process each sequence
                for (seq, point, ty) in insertion_point {
                    let mut body = func.builder_mut().instr_seq(seq);
                    body.instr_at(
                        point,
                        walrus::ir::Call {
                            func: *stubs.clone().get(&ty).unwrap(),
                        },
                    );
                    body.instr_at(
                        point,
                        walrus::ir::Const {
                            value: Value::I32(global_index),
                        },
                    );
                    body.instrs_mut().remove(point + 2);
                    global_index += 1;
                }
            } else {
                // If we are optimizing the binary, we replace indirect calls directly here!
                // We either:
                // 1) Replace the indirect call with a direct call (if value is defined)
                // 2) Replace the indirect call with an unreachable statement if it is never called
                // 3) Keep the indirect call in place as-is
                //
                // We must also keep the number of instructions constant (to handle offsets)
                for (seq, point, ty) in insertion_point {
                    let map_val: &MapValue = modified_map.get(&(global_index as usize)).unwrap();
                    let orig_map_val: &MapValue =
                        original_map.get(&(global_index as usize)).unwrap();
                    let mut body = func.builder_mut().instr_seq(seq);
                    match map_val {
                        // Replace the call
                        MapValue {
                            f_id: Some(id),
                            f_bool: _b,
                        } => {
                            // Remove the indirect call + the idx
                            body.instr_at(point, walrus::ir::Call { func: *id });
                            // We now have Call --> CallIndirect, with "Call" at point
                            body.instrs_mut().remove(point+1);
                        }
                        // Replace the call with `unreachable`
                        MapValue {
                            f_id: None,
                            f_bool: true,
                        } => {
                            body.instr_at(point, walrus::ir::Unreachable {});
                            body.instrs_mut().remove(point + 1);
                        }
                        // Retain the indirect call (no-op)
                        MapValue {
                            f_id: None,
                            f_bool: false,
                        } => {}
                        _ => (),
                    }
                    global_index += 1;
                }
            }
        }
    });

    if !is_opt {
        // Now insert globals to track each call site
        let mut global_map: HashMap<usize, GlobalId> = HashMap::new();
        for idx in 0..(global_index as usize) {
            global_map.insert(
                idx,
                module.globals.add_local(
                    walrus::ValType::I32,
                    true,
                    walrus::InitExpr::Value(Value::I32(-1)),
                ),
            );
        }

        // Now time to go back and modify the indirect call stubs to modify local values
        module.funcs.iter_local_mut().for_each(|(id, func)| {
            if skip_funcs.contains(&id) {
                let args = &func.args.clone();
                let mut func_body = func.builder_mut().func_body();
                for global_idx in 0..global_index as usize {
                    func_body.block_at(0, None, |block| {
                        // Check which call target we are in
                        block
                            .local_get(args[args.len() - 2])
                            .i32_const(global_idx.try_into().unwrap())
                            .binop(BinaryOp::I32Eq)
                            .if_else(
                                None,
                                |then| {
                                    // For each target, we want to check if the previous indirect call
                                    // matches...
                                    then.global_get(*global_map.get(&global_idx).unwrap())
                                        .i32_const(-1)
                                        .binop(BinaryOp::I32Eq)
                                        // if the global == -1, then the function hasn't been called yet!
                                        // we can set the global value...
                                        .if_else(
                                            None,
                                            |then| {
                                                then.local_get(args[args.len() - 3]).global_set(
                                                    *global_map.get(&global_idx).unwrap(),
                                                );
                                            },
                                            |_| {},
                                        )
                                        // if the global != -1 AND global != local, then set global to -2
                                        .local_get(args[args.len() - 3])
                                        .global_get(*global_map.get(&global_idx).unwrap())
                                        .binop(BinaryOp::I32Ne)
                                        .if_else(
                                            None,
                                            |then| {
                                                then.i32_const(-2).global_set(
                                                    *global_map.get(&global_idx).unwrap(),
                                                );
                                            },
                                            |_| {},
                                        );
                                },
                                |else_| {},
                            );
                    });
                }
            }
        });

        // Export all of our globals
        for (idx, g) in global_map {
            module.exports.add(&format!("profiling_global_{}", idx), g);
        }
    }

    let wasm = module.emit_wasm();
    std::fs::write(output, wasm).unwrap();
}
