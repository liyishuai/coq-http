From HTTP Require Export
     Tcp.

Variant traceT :=
  Trace__In  : packetT id -> traceT
| Trace__Out : packetT id -> traceT.

Instance Serialize__traceT : Serialize traceT :=
  fun t =>
    match t with
    | Trace__In  p => [Atom "In "; to_sexp p]
    | Trace__Out p => [Atom "Out"; to_sexp p]
    end%sexp.
