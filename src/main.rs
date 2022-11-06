use walrus::ir::VisitorMut;
use walrus::ir::Instr::*;
use walrus::ir::Value;
use walrus::ir::*;
use walrus::InstrSeqBuilder;
use walrus::TypeId;
use walrus::TableId;
use walrus::FunctionBuilder;
use walrus::ValType;
use walrus::FunctionId;
use std::collections::HashSet;
use std::collections::HashMap;

#[derive(Debug)]
struct TypeScan {
    ty: Vec<(TypeId, TableId)>
}

impl VisitorMut for TypeScan {
    fn visit_instr_mut(&mut self, instr: &mut walrus::ir::Instr, idx: &mut walrus::InstrLocId) {
        //dbg!(&instr);
        match instr {
            CallIndirect(call_indirect) => {
                self.ty.push((call_indirect.ty, call_indirect.table));
            }
            _ => {
            },
        }
    }
}

fn main() {
    let a = std::env::args().nth(1).unwrap();
    let mut module = walrus::Module::from_file(a).unwrap();

    // Scan for all indirect call types
    let types: Vec<Vec<(TypeId, TableId)>> = module.funcs.iter_local_mut().map(|(id, func)| {

        let entry = func.entry_block();
        let mut scan = TypeScan { ty: vec![]  };
        walrus::ir::dfs_pre_order_mut(&mut scan, func, entry);

        scan.ty
    }).collect();

    let mut final_types: HashSet<(TypeId, TableId)> = HashSet::new();
    for ty in types {
        final_types.extend(ty);
    }

    // For each indirect call type generate a new function in the module to serve as a stub
    let mut stubs: HashMap<TypeId, FunctionId> = HashMap::new();
    let mut idx = 0;
    for (ty, tab) in final_types {
        // Look up parameters / results from the type id
        let mut params = Vec::from(module.types.get(ty).params());
        //call target location (for profiling) 
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

        for idx in 1..params.len() {
            func_body.local_get(param_locals[idx]);
        }

        func_body.call_indirect(ty, tab);

        let indirect_stub_id = indirect_stub.finish(param_locals, &mut module.funcs);
        stubs.insert(ty, indirect_stub_id);
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
                            offset += 1;
                        }
                        Block(b) => {
                            seqs_to_process.push(b.seq);
                        }
                        Loop(l) => {
                            seqs_to_process.push(l.seq);
                        }
                        _ => {
                        },
                    }
                    count += 1;
                }
                count = 0;
            }
            drop(body);


            // Process each sequence 
            for (seq, point, ty) in insertion_point {
                let mut body = func.builder_mut().instr_seq(seq);
                body.instr_at(point, walrus::ir::Call {
                                                    func: *stubs.clone().get(&ty)
                                                        .unwrap() 
                                                    });
                body.instr_at(point, walrus::ir::Const{ value: Value::I32(global_index) });
                body.instrs_mut().remove(point+2);
                global_index += 1;
            }
        }
    });

    // Now insert globals to track each call site
    for idx in 0..global_index {
        module.globals.add_local(walrus::ValType::I32, true, walrus::InitExpr::Value(Value::I32(-1)));
    }

    // Now time to go back and modify the indirect call stubs to modify local values
     module.funcs.iter_local_mut().for_each(|(id, func)| {
        if skip_funcs.contains(&id) {
            let func_body = func.builder_mut().func_body();
            // Right now the func body just contains the indirect call at the end
            // For each stub:
            // 1) Check the global index of the call (call target)
            // 2) If the global == -1, then set the value to the call_indirect index
            // 3) If the global != -1, then check if the global value == call_indirect index
            // 3.1) If not, set the global value to -2
            dbg!(&func_body);
        }
    });

    let wasm = module.emit_wasm();
    if let Some(destination) = std::env::args().nth(2) {
        std::fs::write(destination, wasm).unwrap();
    }
}
