open Delimcc

module GreenThreads =
  struct 
    (* à compléter/modifier *)
    type res = 
    Done
    | Yield of continuation
    | Fork of (program*continuation) 
  and continuation = unit->res
    and program=unit->unit
    
let p = new_prompt () 

let scheduler proc_init = 

  let procs = Queue.create () in
  let rec loop = function
      | Done -> if Queue.is_empty procs then () else loop ((Queue.pop procs) ())
      | Yield(c) -> Queue.push c procs; loop ((Queue.pop procs) ())
      | Fork(proc,c) -> Queue.push c procs; spawn proc
        
  and spawn prog = loop (push_prompt p (fun () -> (prog (); Done)))
    in
    spawn proc_init

    let yield () = shift p (fun x -> Yield x)
    let fork proc = shift p (fun x -> Fork (proc,x))
    let exit () = shift p (fun _ -> Done)
  end

  let ping () =
    
    for i = 1 to 10
    do
    print_endline "ping !";
    GreenThreads.yield ()
     done
    

  let pong () =
    for i = 1 to 10
    do
    print_endline "pong !";
    GreenThreads.yield ()
    done
    
 let ping_pong () =
  GreenThreads.fork ping;
  GreenThreads.fork pong

let _ = GreenThreads.scheduler (ping_pong)

module type Channel =
  sig
    val create : unit -> ('a -> unit) * (unit -> 'a)
  end

module GTChannel : Channel =
  struct
    (* à compléter/modifier *)
    let create () = assert false;;
  end
    
let sieve () =
  let rec filter reader =
    GreenThreads.(
      let v0 = reader () in
      if v0 = -1 then exit () else
      Format.printf "%d@." v0;
      yield ();
      let (writer', reader') = GTChannel.create () in
      fork (fun () -> filter reader');
      while true
      do
        let v = reader () in
        yield ();
        if v mod v0 <> 0 then writer' v;
        if v = -1 then exit ()
      done
    ) in
  let main () =
    GreenThreads.(
      let (writer, reader) = GTChannel.create () in
      fork (fun () -> filter reader);
      for i = 2 to 1000
      do
        writer i;
        yield ()
      done;
      writer (-1);
      exit ()
    ) in
  GreenThreads.scheduler main;;
