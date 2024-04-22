using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Microsoft.Dafny {

public class AsyncProofFile {
  private IndDatatypeDecl constants;  // datatype Constants in System module
  private readonly List<Function> appInvPredicates;  // ApplicationInv predicates
  private readonly List<Function> helperFunctions;   // functions and predicates that are not invariants, and not special
  private readonly List<Function> specialHelperFunctions;   // these are predicates containing (v:Variable) and called by appInvPredicates, e.g. Chosen in paxos
  private readonly List<Lemma> invNextLemmas;
  private readonly List<Lemma> helperLemmas;
  public bool hasOwnership;         // protocol has ownership properties
  public Lemma invInductiveLemma;   // InvInductive from sync

  // Constructor
  public AsyncProofFile()
  {
    appInvPredicates = new List<Function>();
    helperFunctions = new List<Function>();
    specialHelperFunctions = new List<Function>();
    invNextLemmas = new List<Lemma>();
    helperLemmas = new List<Lemma>();
    hasOwnership = false;
    invInductiveLemma = null;
  }

  public void AddConstants(IndDatatypeDecl constants) {
    Debug.Assert(this.constants == null, "Hosts already non-null!");
    this.constants = constants;
  }

  // Extract a mapping of HostModulue -> field name in System.Variables
  public Dictionary<string, string> ExtractHosts() {
    Debug.Assert(constants != null, "Variables is null!");
    var res = new Dictionary<string, string>();
    foreach (var formal in constants.GroundingCtor.Formals) {
      if (formal.DafnyName.Contains("Host.Constants")) {
        int startIndex = formal.DafnyName.IndexOf("seq<") + "seq<".Length;
        int endIndex = formal.DafnyName.IndexOf(">", startIndex);
        var substring = formal.DafnyName.Substring(startIndex, endIndex - startIndex);
        var hostModule = substring.Split(".")[0];
        var field = formal.Name;
        res.Add(hostModule, field);
      }
    }
    return res;
  }

  public void AddAppInv(Function predicate) {
    appInvPredicates.Add(predicate);
  }

   public List<Function> GetAppInvPredicates() {
    return appInvPredicates;
  }

  public void AddHelperFunction(Function f) {
    helperFunctions.Add(f);
  }

  public List<Function> GetHelperFunctions() {
    return helperFunctions;
  }

  public void AddSpecialHelperFunction(Function f) {
    specialHelperFunctions.Add(f);
  }

  public List<Function> GetSpecialHelperFunctions() {
    return specialHelperFunctions;
  }

  public void AddInvNextLemma(Lemma lemma) {
    Debug.Assert(lemma.Name.Contains("InvNext"), String.Format("Lemma {0} is not an InvNext lemma", lemma.Name));
    invNextLemmas.Add(lemma);
  }

  public List<Lemma> GetInvNextLemmas() {
    return invNextLemmas;
  }

  public void AddHelperLemma(Lemma lemma) {
    helperLemmas.Add(lemma);
  }

  public List<Lemma> GetHelperLemmas() {
    return helperLemmas;
  }
} // end class DistributedSystemFile


} // end namespace Microsoft.Dafny