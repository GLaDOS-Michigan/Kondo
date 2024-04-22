using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny
{
public class AsyncProofDriver {

  private readonly DafnyOptions options;
  private readonly Program program;
  private readonly AsyncProofFile proofFile;

  // Constructor
  public AsyncProofDriver(DafnyOptions options, Program program)
  {
    this.options = options;
    this.program = program;
    proofFile = new AsyncProofFile();
  }

  public void Resolve() {
    Console.WriteLine(String.Format("Resolving async proof for {0}\n", program.FullName));

    var centralizedProof = GetProofModule();
    proofFile.invInductiveLemma = GetLemma(centralizedProof, "InvInductive");
    ResolveIsOwnership();
    ResolveHosts();
    ResolveApplicationInvariants(centralizedProof);
    ResolveHelperFunctions(centralizedProof);
    ResolveInvNextLemmas(centralizedProof);
    ResolveHelperLemmas(centralizedProof);
  } // end method Resolve()

  // Determines if protocol has ownership properties
  private void ResolveIsOwnership() {
    var hostModules = GetHostModules();
    (bool hasOwn, _) = GetPredicate(hostModules[0], "HostOwnsUniqueKey");
    if (hasOwn) {
      Console.WriteLine("Proof has ownership properties");
      proofFile.hasOwnership = true;
    }
  }

  // Returns the Dafny module with the given name
  private ModuleDefinition GetModule(string moduleName) {
    ModuleDefinition res = null;
    foreach (var kvp in program.ModuleSigs) {
      var moduleDef = kvp.Value.ModuleDef;
      if (moduleDef.DafnyName.Equals(moduleName)) {
        res = moduleDef;
      }
    }
    Debug.Assert(res != null, String.Format("Module {0} not found ", moduleName));
    return res;
  }

  private void ResolveHosts() {
    var systemModule = GetModule("System");

    // Find datatype Constants
    IndDatatypeDecl constsDecl = null;
    foreach (var decl in systemModule.TopLevelDecls.ToList()) {
      if (decl.Name.Equals("Constants")) {
        proofFile.AddConstants((IndDatatypeDecl) decl);
        constsDecl = (IndDatatypeDecl) decl;
        break;
      }
    }
    Debug.Assert(constsDecl != null, "constsDecl should not be null");
  }

  // Resolve list of application invariant predicates
  private void ResolveApplicationInvariants(ModuleDefinition centralizedProof) {

    // get the app inv bundle from centralized
    (bool ok1, Function appInv) = GetPredicate(centralizedProof, "ApplicationInv");
    Debug.Assert(ok1, String.Format("Predicate {0} not found ", "ApplicationInv"));
    
    // extract the conjunct names, and add Function to proofFile
    foreach (var exp in Expression.Conjuncts(appInv.Body)) {
      var predName = exp.ToString().Split('(')[0];  // this is janky
      if (predName != "true") {
        (bool ok2, Function pred) = GetPredicate(centralizedProof, predName);
        Debug.Assert(ok2, String.Format("Predicate {0} not found ", predName));
        proofFile.AddAppInv(pred);
      }
    }
  }

  // Returns the Dafny predicate with the given name in given module
  private (bool, Function) GetPredicate(ModuleDefinition centralizedProof, string predicateName) {
    Function res = null;
    var topLevelFuncs = ModuleDefinition.AllFunctions(centralizedProof.TopLevelDecls.ToList());
    foreach (var topLevelDecl in topLevelFuncs) {
      if (topLevelDecl.Name.Equals(predicateName)) {  // identifying marker for Send Predicate
        res = topLevelDecl;
      }
    }
    if (res != null) {
      return (true, res);
    }
    return (false, null);
  }

  // Returns the Dafny predicate with the given name in given module
  private Lemma GetLemma(ModuleDefinition centralizedProof, string lemmaName) {
    Lemma res = null;
    foreach (var topLevelDecl in ModuleDefinition.AllCallables(centralizedProof.TopLevelDecls.ToList())) {
      if (topLevelDecl is Lemma && ((Lemma) topLevelDecl).Name.Equals(lemmaName)) {  // identifying marker for Send Predicate
        res = (Lemma) topLevelDecl;
      }
    }
    Debug.Assert(res != null, String.Format("Lemma {0} not found ", lemmaName));
    return res;
  }

  // Resolve list of non-invariant functions and predicates
  private void ResolveHelperFunctions(ModuleDefinition centralizedProof) {
    var appInvs = proofFile.GetAppInvPredicates(); // previously resolved application invariants
    string[] reservedNames = {"Inv", "ApplicationInv"};
    foreach (var fn in ModuleDefinition.AllFunctions(centralizedProof.TopLevelDecls.ToList())) {
      if (!appInvs.Contains(fn) && !reservedNames.Contains(fn.Name)) {
        if (IsSpecialHelperFunction(fn)) {
          proofFile.AddSpecialHelperFunction(fn);
        } else {
          proofFile.AddHelperFunction(fn);
        }
      }
    }
  }

  // A special helper lemma is one that is called by an invariant predicate, and 
  // takes (v: Variable) as arugment
  private bool IsSpecialHelperFunction(Function fn) {
    foreach (Formal fm in fn.Formals) {
      if (fm.Type.IsTopLevelTypeWithMembers && fm.Type.AsTopLevelTypeWithMembers.Name == "Variables") {
        foreach (Function invFn in proofFile.GetAppInvPredicates()) {
          var wr = new StringWriter();
          var printer = new Printer(wr, options);
          printer.PrintFunction(invFn, 0, false, 0);
          var invFnStr = wr.ToString();
          if (invFnStr.Contains($"{fn.Name}(")) {
            return true;
          }
        }
      }
    }   
    return false;
  }

  private void ResolveInvNextLemmas(ModuleDefinition centralizedProof) {
    foreach (var topLevelDecl in ModuleDefinition.AllCallables(centralizedProof.TopLevelDecls.ToList())) {
      if (topLevelDecl is Lemma && ((Lemma) topLevelDecl).Name.Contains("InvNext")) {
        proofFile.AddInvNextLemma((Lemma) topLevelDecl);
      }
    }
  }

  private void ResolveHelperLemmas(ModuleDefinition centralizedProof) {
    string[] reservedNames = {"InvImpliesSafety", "InitImpliesInv", "InvInductive"};
    foreach (var topLevelDecl in ModuleDefinition.AllCallables(centralizedProof.TopLevelDecls.ToList())) {
      if (topLevelDecl is Lemma && !((Lemma) topLevelDecl).Name.StartsWith("InvNext") && !reservedNames.Contains(((Lemma) topLevelDecl).Name)) {
        proofFile.AddHelperLemma((Lemma) topLevelDecl);
      }
    }
  }

  // Returns the centralized Proof module
  private ModuleDefinition GetProofModule() {
    ModuleDefinition res = null;
    foreach (var kvp in program.ModuleSigs) {
      var moduleDef = kvp.Value.ModuleDef;
      if (moduleDef.DafnyName.Contains("Proof")) {
        res = moduleDef;
      }
    }
    Debug.Assert(res != null, "Proof module not found ");
    return res;
  }

  // Returns the all HostModules
  private List<ModuleDefinition> GetHostModules() {
    List<ModuleDefinition> res = new List<ModuleDefinition>();
    foreach (var kvp in program.ModuleSigs) {
      var moduleDef = kvp.Value.ModuleDef;
      if (moduleDef.DafnyName.Contains("Host")) {
        res.Add(moduleDef);
      }
    }
    Debug.Assert(res.Count != 0, "Proof module not found ");
    return res;
  }


  public void WriteToFile() {
    string proofString = AsyncProofPrinter.PrintAsyncProof(proofFile, options, program.FullName);
    string proofOutputFullname = Path.GetDirectoryName(program.FullName) + "/../async-kondo/applicationProofDraftAutogen.dfy";
    Console.WriteLine(string.Format("Writing async proof draft to {0}", proofOutputFullname));
    File.WriteAllText(proofOutputFullname, proofString);
  }
}  // end class MessageInvariantsDriver
} // end namespace Microsoft.Dafny