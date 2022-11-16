use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;
use std::hash::Hasher;
use walrus::ir::Instr::*;
use walrus::ir::*;
use walrus::FunctionKind::Import;
use walrus::*;

#[derive(Debug, Clone)]
pub struct FastCallScan {
    is_fastcall: bool,
    // keep track of ambiguous calls
    deps: HashSet<FunctionId>,
    func_id: FunctionId,
    imported_funcs: HashSet<FunctionId>,
    all_funcs: Vec<(FunctionId, Type)>,
    all_types: HashMap<TypeId, Type>,
}

impl Hash for FastCallScan {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.func_id.hash(state);
    }
}
impl PartialEq for FastCallScan {
    fn eq(&self, other: &Self) -> bool {
        self.func_id == other.func_id
    }
}
impl Eq for FastCallScan {}

impl VisitorMut for FastCallScan {
    fn visit_instr_mut(&mut self, instr: &mut walrus::ir::Instr, idx: &mut walrus::InstrLocId) {
        match instr {
            // any indirect call automatically taints our fastcall opt pass
            CallIndirect(call_indirect) => {
                // Add all possible targets based on type signature
                // *Unless* one of those targets is actually recursive!
                let all: Vec<&FunctionId> = self
                    .all_funcs
                    .iter()
                    // Ignore functions which don't match the call target
                    .filter(|(x, y)| y == self.all_types.get(&call_indirect.ty).unwrap())
                    .map(|(x, y)| x)
                    .collect();
                for call in &all {
                    if **call == self.func_id {
                        self.is_fastcall = false;
                        return;
                    }
                }
                // Else, extend
                self.deps.extend(all.clone());
            }
            // Keep track of each call that we make
            Call(idx) => {
                // Recursive calls taint our fastcall pass
                if self.func_id == idx.func {
                    self.is_fastcall = false;
                } else if self.imported_funcs.contains(&idx.func) {
                    self.is_fastcall = false;
                } else {
                    // if the call isn't recursive && isn't a system call, add it as a possible
                    // dependency
                    self.deps.insert(idx.func);
                }
            }
            _ => {}
        }
    }
}

fn contains_slowcall(scan: &FastCallScan, slowset: &HashSet<&FastCallScan>) -> bool {
    slowset.contains(scan)
}

fn check_fastcall_deps(scan: &FastCallScan, fastset: &HashSet<&FastCallScan>) -> bool {
    let mut fset = HashSet::new();
    for call in fastset {
        fset.insert(call.func_id);
    }
    scan.deps
        .iter()
        .filter(|x| fset.contains(x))
        .collect::<Vec<&FunctionId>>()
        .len()
        == scan.deps.len()
}

fn type_lookup(ty_id: TypeId, module: &Module) -> Type {
    module.types.get(ty_id).clone()
}

pub fn compute_slowcalls(module: &mut Module) -> HashSet<FunctionId> {
    let mut set = HashSet::new();

    // Get the WASI/system call func ids
    let mut imported_funcs = HashSet::new();
    module.imports.iter().for_each(|func| match func.kind {
        ImportKind::Function(f_id) => {
            // We optimize out fd_write in most of our benchmarks + proc_exit
            if func.name != "proc_exit" && func.name != "fd_write" {
                imported_funcs.insert(f_id);
            }
        }
        _ => (),
    });

    let mod_funcs: Vec<(FunctionId, Type)> = module
        .funcs
        .iter()
        .map(|x| (x.id(), type_lookup(x.ty(), module)))
        .collect();

    let types: Vec<(TypeId, Type)> = module.types.iter().map(|x| (x.id().clone(), x.clone())).collect();
    let mut mod_types = HashMap::new();
    for (ty_id, ty) in types {
        mod_types.insert(ty_id, ty);
    }

    let mut scan_results = vec![];
    module.funcs.iter_local_mut().for_each(|(id, func)| {
        let entry = func.entry_block();
        let mut scan = FastCallScan {
            is_fastcall: true,
            func_id: id,
            deps: HashSet::new(),
            imported_funcs: imported_funcs.clone(),
            all_funcs: mod_funcs.clone(),
            all_types: mod_types.clone(),
        };
        walrus::ir::dfs_pre_order_mut(&mut scan, func, entry);
        scan_results.push(scan);
    });

    // Each func is now in one of three states
    // 1) Confirmed to be a fastcall
    // 2) Confirmed to be a slowcall
    // 3) Ambiguous

    // We only want to instrument known *slowcalls*
    // First, create a separate set of known fastcalls (remove these from the primary set as well)
    let mut fastcalls: HashSet<&FastCallScan> = scan_results
        .iter()
        .filter(|x| x.is_fastcall == true && x.deps.len() == 0)
        .collect();
    let mut slowcalls: HashSet<&FastCallScan> = scan_results
        .iter()
        .filter(|x| x.is_fastcall == false)
        .collect();

    // Contains ambiguous calls
    let mut unknown: HashSet<&FastCallScan> = scan_results
        .iter()
        .filter(|x| x.is_fastcall == true && x.deps.len() > 0)
        .collect();
    // Next, loop over the set of ambiguous calls, checking to see if any of them can be optimized
    let mut prev = 0;
    while unknown.len() != prev {
        prev = unknown.len();
        {
            // Now filter to find the slowcalls
            let slow = unknown
                .iter()
                .filter(|x| contains_slowcall(&x, &slowcalls))
                .collect::<HashSet<&&FastCallScan>>();
            for call in &slow {
                slowcalls.insert(call);
            }

            // Find the confirmed fastcalls
            let fast = unknown
                .iter()
                .filter(|x| check_fastcall_deps(&x, &fastcalls))
                .collect::<HashSet<&&FastCallScan>>();
            for call in fast {
                fastcalls.insert(call);
            }
        }
        // Adjust which calls we don't know about yet
        for call in &slowcalls {
            unknown.remove(call);
        }
        for call in &fastcalls {
            unknown.remove(call);
        }
    }

    // At this point any remaining calls that are still unknown must be slowcalls
    for call in &unknown {
        slowcalls.insert(call);
    }

    for call in &slowcalls {
        set.insert(call.func_id);
    }

    // Note these numbers won't match *exactly* to VV's output on the same binary
    // This is because VV performs some extra optimizations around indirect calls
    println!(
        "Speculatively identified {} fastcalls and {} slowcalls",
        fastcalls.len(),
        slowcalls.len()
    );

    set
}

struct CallScanner {
    mapping: HashMap<FunctionId, FunctionId>,
}

impl VisitorMut for CallScanner {
    fn visit_instr_mut(&mut self, instr: &mut walrus::ir::Instr, idx: &mut walrus::InstrLocId) {
        match instr {
            Call(idx) => match self.mapping.get(&idx.func) {
                Some(new_idx) => {}
                _ => (),
            },
            _ => {}
        }
    }
}

/*
 * For each slowcall, we need to:
 * 1) Generate a new function stub for each slowcall
 *  1.1) Each function stub must increment a global counter
 * 2) Replace all function call points with a call to our stub instead
 */
pub fn generate_slowcall_stubs(
    module: &mut Module,
    slowcalls: &HashSet<FunctionId>,
    slowcall_ctr: &GlobalId,
) -> () {
    let mut func_mapping = HashMap::new();
    let mut call_stub_ctr = 0;
    for func in slowcalls {
        let ty = module.types.get(module.funcs.get(*func).ty()).clone();
        let mut call_stub = FunctionBuilder::new(&mut module.types, &ty.params(), &ty.results());
        call_stub.name(format!("slowcall_stub_{}", call_stub_ctr));
        call_stub_ctr += 1;

        let mut param_locals = vec![];
        for p in ty.params() {
            let n = module.locals.add(*p);
            param_locals.push(n);
        }

        let mut func_body = call_stub.func_body();

        // Increment the slowcall ctr
        func_body
            .global_get(*slowcall_ctr)
            .i32_const(1)
            .binop(BinaryOp::I32Add)
            .global_set(*slowcall_ctr);

        for idx in 0..(param_locals.len()) {
            func_body.local_get(param_locals[idx]);
        }
        func_body.call(*func);

        let new_stub_id = call_stub.finish(param_locals, &mut module.funcs);
        func_mapping.insert(*func, new_stub_id);
    }

    // Now that we have generated the stubs, we need to  replace the actual calls in the program
    module.funcs.iter_local_mut().for_each(|(id, func)| {
        let entry = func.entry_block();
        let mut scan = CallScanner {
            mapping: func_mapping.clone(),
        };
        walrus::ir::dfs_pre_order_mut(&mut scan, func, entry);
    });
}
