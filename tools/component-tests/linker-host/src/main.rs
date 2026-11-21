//! `linker-host <component.wasm>`: supply the root import `f` as a wasmtime `Linker` host
//! function (`func_wrap`, Rust type `(u32,) -> ()`, which logs its argument), instantiate the
//! component and call its export `get: func() -> u32`. Prints the outcome and the host log.
use std::sync::{Arc, Mutex};
use wasmtime::component::{Component, Linker};
use wasmtime::{Config, Engine, Store};

fn main() -> anyhow::Result<()> {
    let path = std::env::args().nth(1).expect("usage: linker-host <component.wasm>");
    let engine = Engine::new(&Config::new())?;
    let comp = Component::from_file(&engine, &path)?;
    let log = Arc::new(Mutex::new(Vec::<u32>::new()));
    let mut linker: Linker<()> = Linker::new(&engine);
    let l2 = log.clone();
    linker.root().func_wrap("f", move |_, (x,): (u32,)| {
        l2.lock().unwrap().push(x);
        Ok(())
    })?;
    let mut store = Store::new(&engine, ());
    match linker.instantiate(&mut store, &comp) {
        Err(e) => println!("instantiate: error: {e:#}"),
        Ok(inst) => {
            println!("instantiate: ok; host log {:?}", log.lock().unwrap());
            let get = inst.get_typed_func::<(), (u32,)>(&mut store, "get")?;
            let (v,) = get.call(&mut store, ())?;
            println!("get() = {v}; host log {:?}", log.lock().unwrap());
        }
    }
    Ok(())
}
