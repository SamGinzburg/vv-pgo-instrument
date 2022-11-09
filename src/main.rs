mod profilemap;
mod instrument;

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
use profilemap::process_map;
use profilemap::MapValue;
use instrument::generate_stubs;

#[derive(Deserialize, Debug)]
pub struct Profile {
    map: HashMap<usize, Vec<i32>>,
}

#[derive(Debug)]
struct TypeScan {
    ty: Vec<(TypeId, TableId)>,
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

    let indirect_window = 5;
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
    //dbg!(&map);

    let mut module = walrus::Module::from_file(input).unwrap();

    // We need to map the profiling data to FunctionId refs in the AST
    // We parse table 0, get the offset, and then iterate through the functions
    let mut modified_map: HashMap<usize, MapValue> = HashMap::new();
    //let tab_id = module.tables.main_function_table().unwrap().unwrap();
    //let table = module.tables.get(tab_id);
    if is_opt {
        process_map(&module, &map, &mut modified_map);
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

    // Generate stubs to replace indirect calls + add instrumentation
    generate_stubs(&mut module,
                   &mut final_types,
                   &mut stubs,
                   &mut modified_map,
                   &map,
                   is_opt);

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
                        IfElse(if_else) => {
                            seqs_to_process.push(if_else.consequent);
                            seqs_to_process.push(if_else.alternative);
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
                            // id should be a vec of size 1
                            assert!(id.len() == 1, "id is of len: {}", id.len());
                            body.instr_at(point, walrus::ir::Call { func: id[0] });
                            // We now have Call --> CallIndirect, with "Call" at point
                            body.instrs_mut().remove(point+1);
                        }
                        // Replace the call with `unreachable`
                        MapValue {
                            f_id: None,
                            f_bool: true,
                        } => {
                            body.instr_at(point, walrus::ir::Unreachable {});
                            body.instrs_mut().remove(point+1);
                        }
                        // Retain the indirect call (no-op)
                        MapValue {
                            f_id: None,
                            f_bool: false,
                        } => {
                            println!("retaining call...");
                        }
                        _ => {
                            panic!("unhandled case: {:?}", map_val);
                        },
                    }
                    global_index += 1;
                }
            }
        }
    });

    if !is_opt {
        // Now insert globals to track each call site
        let mut global_map: HashMap<usize, Vec<GlobalId>> = HashMap::new();
        // Insert X many globals per-call site
        // We do this to track cases where just a few different targets are possible
        for idx in 0..(global_index as usize) {
            let mut new_globals = vec![];
            for inner_idx in 0..indirect_window {
                new_globals.push(module.globals.add_local(
                    walrus::ValType::I32,
                    true,
                    walrus::InitExpr::Value(Value::I32(-1)),
                ));
            }
            global_map.insert(
                idx, // e.g., Map 0,1,2,3,4 --> to the same call site to mimic an array
                new_globals,
            );
        }

        // Create a global for tracking "slowcalls"
        // Every time we call a function that VV can't optimize we will inc this counter
        let slowcalls_id = module.globals.add_local(
                    walrus::ValType::I32,
                    true,
                    walrus::InitExpr::Value(Value::I32(-1)),
                );
        // Construct a mapping of function id ==> bools, to identify fastcalls
        // TODO


        // Now time to go back and modify the indirect call stubs to modify local values
        for function_idx in skip_funcs {
            let id = function_idx;
            let func = module.funcs.get_mut(function_idx).kind.unwrap_local_mut();
            let args = &func.args.clone();
            let call_target = args[args.len() - 1];
            let indirect_call_value = args[args.len() - 2];
            let mut func_builder = func.builder_mut();
            let mut func_body = func_builder.func_body();
            //let local_vals = stub_locals.get(&id).unwrap();
            //let counter = local_vals[0];
            //let set_value =  local_vals[1];
            //let counter = module.locals.add(ValType::I32);
            let set_value = module.locals.add(ValType::I32);
            func_body.block_at(0, None, |block| {
                block.global_get(slowcalls_id)
                     .i32_const(1).binop(BinaryOp::I32Add)
                     .global_set(slowcalls_id);
            });
            drop(func_body);
            let mut block_seq = func_builder.dangling_instr_seq(None);
            let block_seq_id = block_seq.id();
            for global_idx in 0..global_index as usize {
                /*
                 * We have an array of values representing each call site
                 * We "iterate" through the "array" to find an open slot
                 *
                 * For each slot:
                 * if the matching global is -1, set the value ( and set_value <- true) 
                 *  after setting, we break out.
                 *
                 * if after falling through all available slots, set_value != true
                 * set all globals for this call site to -2
                 *
                 */
                for array_value in global_map.get(&global_idx).unwrap() {
                    block_seq.block(None, |block| {
                        // Check which call target we are in
                        block
                            .local_get(call_target)
                            .i32_const((global_idx).try_into().unwrap())
                            .binop(BinaryOp::I32Eq)
                            .if_else(
                                None,
                                |then| {
                                    // For each target, we want to check if the previous indirect call
                                    // matches...
                                        then
                                        .global_get(*array_value)
                                        .i32_const(-1)
                                        .binop(BinaryOp::I32Eq)
                                        // OR if the value is already set
                                        .global_get(*array_value)
                                        .local_get(indirect_call_value)
                                        .binop(BinaryOp::I32Eq)
                                        .binop(BinaryOp::I32Or)
                                        // if the global == -1, then the function hasn't been called yet!
                                        // we can set the global value...
                                        .if_else(
                                            None,
                                            |then| {
                                                then.local_get(indirect_call_value)
                                                    .global_set(
                                                    *array_value,
                                                )
                                                .i32_const(1)
                                                .local_set(set_value)
                                                .br(block_seq_id);
                                            },
                                            |_| {},
                                        );
                                },
                                |else_| {},
                            );
                    });
                }
            }
            drop(block_seq);
            let mut func_body = func_builder.func_body();
            func_body.instr_at(1, walrus::ir::Instr::Block ( walrus::ir::Block { seq: block_seq_id } ) );
            // now check if we failed to set any of the slots for our call target
            // we have to do this for each call target all over again...
            for global_idx in 0..global_index as usize {
                let arr = global_map.get(&(global_idx as usize)).unwrap();
                func_body
                .local_get(indirect_call_value)
                .i32_const((global_idx).try_into().unwrap())
                .binop(BinaryOp::I32Eq)
                .if_else(None, |then| {
                    then
                    .local_get(set_value)
                    .i32_const(1)
                    .binop(BinaryOp::I32Ne)
                    .if_else(None, |then| {
                        for idx in 0..indirect_window {
                            //then
                            //.i32_const(-2)
                            //.global_set(arr[idx]);
                        }
                    }, |_| {});
                }, |_| {});
            }
        }

        // Now that we have instrumented the indirect calls,
        // we will instrument the regular slowcalls

        module.exports.add(&format!("slowcalls"), slowcalls_id);
        // Export all of our globals
        for (idx, g) in global_map {
            // We represent each callsite using multuple global values
            for inner_idx in 0..g.len() {
                module.exports.add(&format!("profiling_global_{}_{}", idx, inner_idx), g[inner_idx]);
            }
        }
    }


    let wasm = module.emit_wasm();
    std::fs::write(output, wasm).unwrap();
}
