  session VeriComp in "Lib/VeriComp" = "HOL-Library" +
  theories
    Compiler
    Fixpoint

session Locale_Code in "Lib/Locale_Code" = "HOL-Library" +
  theories
    Locale_Code

session Fresh in "Lib/Fresh" = "HOL-Library" +
  theories
    Fresh
    Fresh_String

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

chapter "veriopt"

session CodeGen in CodeGen = Locale_Code +
  options [document = pdf, document_output = "output",
           document_variants="document:outline=/proof",
           show_question_marks = false]
  directories
    Examples
  theories
    Rewritable
    MatchPattern
    JavaExport
    Stratego
    "Examples/Arithmetic"
    "Examples/ArithmeticStratego"
  document_files (in "../latex")
    "root.tex"
    "mathpartir.sty"

session Graph in Graph = VeriComp +
  description
    "GraalVM Intermediate Representation encoding"
  options [document = pdf, document_output = "output",
           show_question_marks = false]
  theories
    JavaWords
    JavaLong

    Values
    ValueThms
    Stamp
    IRNodes
    IRNodeHierarchy
    IRGraph
    Comparison
    Traversal
    Class
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
    Snippets
  theories
    Form
    IRGraphFrames
    IRStepObj
    IRStepThms
    IRTreeEval
    IRTreeEvalThms
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
           show_question_marks = false,
           quick_and_dirty,
           document_variants="document:outline=/proof"]
  sessions
    Snippets
    Fresh
    CodeGen
  theories
    Markup
    Phase
    Canonicalization
    CodeGen
    
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


session Document in "Papers/Main" = Canonicalizations +
  description
    "Whole project document"
  options [quick_and_dirty,
           document = pdf, document_output = "output",
           show_question_marks = false,
           document_variants="document:outline=/proof"]
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
    Graph.JavaWords
    Graph.JavaLong
    Graph.Values
    Graph.ValueThms
    Graph.Stamp

    Graph.IRNodes
    Graph.IRNodeHierarchy
    
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
  document_theories
    Graph.JavaWords
    Graph.JavaLong
    Graph.Values
    Graph.ValueThms
    Graph.Stamp

    Graph.IRNodes
    Graph.IRNodeHierarchy
    
    Graph.IRGraph

    Semantics.IRTreeEval
    Semantics.IRTreeEvalThms
    Semantics.TreeToGraph
    Semantics.Form
    Semantics.IRGraphFrames
    Semantics.TreeToGraphThms
    Semantics.IRStepObj
    Semantics.IRStepThms

    Proofs.StampEvalThms

    OptimizationDSL.Markup
    OptimizationDSL.Phase
    OptimizationDSL.Canonicalization

    Canonicalizations.Common
    (*Canonicalizations.AbsPhase*)
    Canonicalizations.AddPhase
    Canonicalizations.AndPhase
    Canonicalizations.NewAnd
    Canonicalizations.BinaryNode
    Canonicalizations.ConditionalPhase
    Canonicalizations.MulPhase
    Canonicalizations.NotPhase
    Canonicalizations.OrPhase
    Canonicalizations.SubPhase
    Canonicalizations.XorPhase
  document_files (in ".")
    "root.tex"
  document_files (in "../../latex")
    "mathpartir.sty"


session ValidationPaperSnippets in "Papers/Validation" = ConditionalElimination +
  description
    "Snippets of Isabelle theories used for the preparation of the future paper ``Validating Faithful Formalization of an Existing Compiler''"
  options [document = pdf, document_output = "output",
           show_question_marks = false, quick_and_dirty]
  sessions
    Snippets
  theories
    IRGraphSort
    ValidationSnippets
  document_files (in "../../latex")
    "root.tex"
    "mathpartir.sty"


session CodeGenPaper in "Papers/CodeGen" = OptimizationDSL +
  description
    "Snippets of Isabelle theories used for a paper on the code generation facilities"
  options [document = pdf, document_output = "output",
           show_question_marks = false, quick_and_dirty]
  sessions
    Snippets
  theories
    IRExprCodeGen
  document_files (in "../../latex")
    "root.tex"
    "mathpartir.sty"
