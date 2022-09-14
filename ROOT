chapter "veriopt"

session Graph in Graph = "HOL-Library" +
  description
    "GraalVM Intermediate Representation encoding"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    Comparison
    IRGraph
    IRNodeHierarchy
    IRNodes
    Long
    Stamp
    Traversal
    Values
    ValueThms
  document_files (in "../latex")
    "root.tex"
    "mathpartir.sty"

session Semantics in Semantics = Graph +
  description
    "Semantics of the GraalVM IR"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  sessions
    "HOL-Eisbach"
  theories
    Form
    IRGraphFrames
    IRStepObj
    IRStepThms
    IRTreeEval
    IRTreeEvalThms
    (*TermRewrites*)
    TreeToGraph
    TreeToGraphThms
  document_files (in "../latex")
    "root.tex"
    "mathpartir.sty"

session Proofs in Proofs = Semantics +
  description
    "Supporting proof theories and definitions"
  sessions
    Snippets
  theories
    Bisimulation
    Rewrites
    StampEvalThms
    Stuttering

session OptimizationDSL in "Optimizations/DSL" = Proofs +
  description
    "DSL for expressing optimizations"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  sessions
    Snippets
  theories
    Markup
    Phase
    Canonicalization
  document_files (in "../../latex")
    "root.tex"
    "mathpartir.sty"

session Canonicalizations in "Optimizations/Canonicalizations" = OptimizationDSL +
  description
    "Canonicalization phase"
  options [document = pdf, document_output = "output",
           show_question_marks = false, quick_and_dirty]
  theories
    Common

    AbsPhase
    AddPhase
    AndPhase
    BinaryNode
    ConditionalPhase
    MulPhase
    NewAnd
    NotPhase
    OrPhase
    ShiftPhase
    SignedDivPhase
    SignedRemPhase
    SubPhase
    XorPhase

    ProofStatus
  document_files (in "../../latex")
    "root.tex"
    "mathpartir.sty"

session ConditionalElimination in "Optimizations/ConditionalElimination" = Proofs +
  description
    "(experimental) Conditional elimination phase"
  options [quick_and_dirty,
           document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    ConditionalElimination
  document_files (in "../../latex")
    "root.tex"
    "mathpartir.sty"

session Optimizations in Optimizations = OptimizationDSL +
  description
    "(deprecated) Graph transformation optimizations"
  options [quick_and_dirty] (* Many sorries in CanonicalizationTreeProofs but all in experiment *)
  theories
    CanonicalizationTree
    CanonicalizationTreeProofs
    CanonicalizationSyntax

(*session Tests in Tests = Semantics +
  description
    "Miscellaneous project testing"
  theories
    (*AssertTesting*)
    (*ExecExamples*)
    UnitTesting
    (*Test: ArithmeticTesting*)
    (*ConditionalEliminationTests*)*)

\<comment>\<open>Documentation sessions\<close>

session Snippets = "HOL-Library" +
  description
    "Additional commands to enable the generation of LaTeX snippets of theories"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    Snipping
  document_files (in "./latex")
    "root.tex"
    "mathpartir.sty"


session Document in "Papers/Main" = Canonicalizations +
  description
    "Whole project document"
  options [quick_and_dirty,
           document = pdf, document_output = "output",
           show_question_marks = false]
  sessions
    Graph
    Semantics
    Proofs
    OptimizationDSL
    Canonicalizations
    ConditionalElimination
  theories
    ConditionalElimination.ConditionalElimination
  document_theories
    Graph.Values
    Graph.IRNodes
    Graph.IRNodeHierarchy
    Graph.Stamp
    Graph.IRGraph
    Graph.Traversal
    Graph.Comparison

    Semantics.IRTreeEval
    Semantics.IRTreeEvalThms
    Semantics.TreeToGraph
    Semantics.Form
    Semantics.IRGraphFrames
    Semantics.TreeToGraphThms
    Semantics.IRStepObj
    Semantics.IRStepThms

    Proofs.Bisimulation
    Proofs.Rewrites
    Proofs.Stuttering
    Proofs.StampEvalThms

    OptimizationDSL.Markup
    OptimizationDSL.Phase
    OptimizationDSL.Canonicalization

    Canonicalizations.Common
    Canonicalizations.AbsPhase
    Canonicalizations.AddPhase
    Canonicalizations.AndPhase
    Canonicalizations.BinaryNode
    Canonicalizations.ConditionalPhase
    Canonicalizations.MulPhase
    Canonicalizations.NewAnd
    Canonicalizations.NotPhase
    Canonicalizations.OrPhase
    Canonicalizations.ShiftPhase
    Canonicalizations.SignedDivPhase
    Canonicalizations.SignedRemPhase
    Canonicalizations.SubPhase
    Canonicalizations.XorPhase

    ConditionalElimination.ConditionalElimination
  document_files (in ".")
    "root.tex"
  document_files (in "../Stamps")
    "lattice.tex"
  document_files (in "../../latex")
    "mathpartir.sty"


\<comment>\<open>Snippets for papers\<close>

(* Currently preserved in atva branch 
session SemanticsPaper in "Papers/Semantics" = Optimizations +
  description
    "Content for IR semantics description paper"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    SemanticsSnippets
  document_files (in "../../latex")
    "root.tex"
    "mathpartir.sty"
*)


session StampLattice in "Papers/Stamps" = Graph +
  description
    "(experimental) Investigation of an alternative approach to representing stamps in Isabelle/HOL"
  options [quick_and_dirty,
           document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    Graph.StampLattice
  document_theories
    Graph.StampLattice
  document_files (in ".")
    "root.tex"
    "lattice.tex"
  document_files (in "../../latex")
    "mathpartir.sty"


session TreePaperSnippets in "Papers/Tree" = Canonicalizations +
  description
    "Snippets of Isabelle theories used for the preparation of the future paper ``Verifying term graph optimizations using Isabelle/HOL''"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  sessions
    Snippets
  theories
    TreeSnippets
    SlideSnippets
  document_files (in "../../latex")
    "root.tex"
    "mathpartir.sty"
