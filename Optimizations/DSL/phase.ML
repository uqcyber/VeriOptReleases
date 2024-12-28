(*  Title:      Optimizations/DSL/phase.ML
    Author:     Brae Webb

Organisation of rules into phases.
*)

signature Rule =
sig
  type T
  val pretty: Proof.context -> bool -> T -> Pretty.T
  val is_proved: T -> bool
end

signature DSL_PHASE =
sig
type T;

type phase =
  {name: binding,
   trm: term,
   rules: (binding, T) Map.map}

type config = (binding * string)

val current: theory -> phase option
val phases: theory -> phase list
val register: (binding * T) -> theory -> theory

val enter: config -> theory -> Proof.context
val exit: local_theory -> local_theory
val setup: config -> theory -> local_theory

val pretty: bool -> phase -> Proof.context -> Pretty.T
val summary: phase -> Proof.context -> (int * int)

end;

functor DSL_Phase(Rule: Rule): DSL_PHASE =
struct
type T = Rule.T

type phase =
  {name: binding,
   trm: term,
   rules: (binding, T) Map.map}

type store = (binding, phase) Map.map

datatype status =
  NoPhase |
  InPhase of binding

type state =
  {store: store,
   status: status}

type config = (binding * string)


val empty = {store=Map.empty, status=NoPhase};

fun merge_statuses (NoPhase, NoPhase) = NoPhase
  | merge_statuses (NoPhase, InPhase name) = InPhase name
  | merge_statuses (InPhase name, NoPhase) = InPhase name
  | merge_statuses (InPhase _, InPhase _) = raise ERROR "oh no"

structure PhaseData = Theory_Data
(
  type T = state;
  val empty = empty;
  fun merge (lhs, rhs) = 
    {status=merge_statuses (#status lhs, #status rhs),
     store= Map.merge (#store lhs) (#store rhs)}
);

val state = PhaseData.get;

fun phase_name thy = 
  (case #status (state thy) of
    NoPhase => NONE
    | InPhase name => SOME name)

fun phase_by_name data name : phase option =
  let
    val lookup = snd (#store data);
  in
    case name of
      NONE => NONE
      | SOME n => lookup n
  end

fun current thy = 
  let
    val phase = phase_name thy;
  in
    phase_by_name (state thy) phase
  end

fun phases thy = Map.values (#store (state thy))

fun expand_phase rule (phase: phase): phase =
  {name = (#name phase), trm = (#trm phase),
    rules = Map.insert (#rules phase) rule}

fun insert_rule' t phase data =
  let
    val phase' = expand_phase t phase;
    val data' = Map.insert (#store data) (#name phase, phase')
  in
    {status= #status data, store= data'}
  end

fun insert_rule t data =
  let
    val phase = (case (#status data) of
      NoPhase => raise TERM ("Optimization phase missing", []) |
      InPhase name => phase_by_name data (SOME name)
    );
    val data' = (case phase of
      NONE => raise TERM ("Optimization phase missing", []) |
      SOME phase => insert_rule' t phase data
    );
  in
    data'
  end

fun register t thy = PhaseData.map (insert_rule t) thy

fun new_phase name trm = {name = name, trm = trm, rules = Map.empty};

fun enter' name trm thy = PhaseData.map (fn state =>
  case (#status state) of
    NoPhase => {status=InPhase name, store=Map.insert (#store state) (name, new_phase name trm)} |
    InPhase _ => raise TERM ("optimization phase already established", [])
  ) thy

fun enter (name, trm) thy =
  Proof_Context.init_global (enter' name (Syntax.read_term_global thy trm) thy)

fun exit' thy = PhaseData.map (fn state =>
  case (#status state) of
    NoPhase => raise TERM ("no phase to exit", []) |
    InPhase _ => {status=NoPhase, store=(#store state)}
  ) thy

val exit = Local_Theory.background_theory exit'

fun pretty_bind binding =
  Pretty.markup 
    (Position.markup (Binding.pos_of binding) Markup.position)
    [Pretty.str (Binding.name_of binding)];

fun pretty_phase obligation (phase:phase) ctxt =
  Pretty.block 
    [Pretty.str "phase: ", pretty_bind (#name phase), Pretty.fbrk,
     Pretty.str "trm: ", Syntax.pretty_term ctxt (#trm phase), Pretty.fbrk,
     Pretty.big_list "rules:" (map (Rule.pretty ctxt obligation) (Map.values (#rules phase)))]

fun pretty obligation phase ctxt =
  pretty_phase obligation phase ctxt

fun fold_pairs (cx, cy) (tx, ty) = (cx + tx, cy + ty)
fun is_proved r = if Rule.is_proved r then 1 else 0;

fun summary (phase:phase) _ =
  (fold fold_pairs (map (fn r => (is_proved r, 1))(Map.values (#rules phase))) (0, 0))

fun pretty' state ctxt =
  case (#status state) of
    NoPhase => Pretty.str "No phase" |
    InPhase name => 
      (case Map.lookup (#store state) name of
        NONE => raise ERROR "Bug" |
        SOME phase => pretty_phase false phase ctxt
      )

fun pretty'' ctxt =
  [pretty' (state (Proof_Context.theory_of ctxt)) ctxt]

fun setup config thy =
  Local_Theory.init 
    {background_naming = Sign.naming_of thy,
        setup = enter config,
        conclude = exit}
    {define = Generic_Target.define Generic_Target.theory_target_foundation,
        notes = Generic_Target.notes Generic_Target.theory_target_notes,
        abbrev = Generic_Target.abbrev Generic_Target.theory_target_abbrev,
        declaration = K Generic_Target.theory_declaration,
        theory_registration =  Generic_Target.theory_registration,
        locale_dependency = fn _ => error "Not possible in instantiation target",
        pretty = pretty''}
    thy

end