using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Runtime.Intrinsics.X86;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.Dafny.ProofObligationDescription;
using Newtonsoft.Json;

namespace Microsoft.Dafny
{
public static class AsyncProofPrinter {

  private static readonly string[] Includes = {"monotonicityInvariantsAutogen.dfy", "messageInvariantsAutogen.dfy"};
  private static readonly string[] Imports = {"Types", "UtilitiesLibrary", "MonotonicityLibrary", "DistributedSystem", "MonotonicityInvariants", "MessageInvariants", "Obligations"};
  private static readonly string DafnyRoot = $"{System.AppDomain.CurrentDomain.BaseDirectory}/../";
  private static readonly string TemplatePath = $"{DafnyRoot}/Source/DafnyCore/Kondo/templates.json";

  private static readonly Dictionary<string, string[]> Template = JsonConvert.DeserializeObject<Dictionary<string, string[]>>(File.ReadAllText(TemplatePath));

  private static string GetFromTemplate(string key, int indent) {
    var lines = Template[key];
    var res = new StringBuilder();
    foreach (var l in lines) {
      res.AppendLine(new string(' ', indent) + l);
    }
    return res.ToString();
  }

  public static string PrintAsyncProof(AsyncProofFile file, DafnyOptions options, string sourceFileName) {
    var res = new StringBuilder();

    // Header
    res.AppendLine($"/// This file is auto-generated from {sourceFileName}");
    res.AppendLine($"/// Generated {DateTime.Now.ToString("MM/dd/yyyy HH:mm")} {TimeZoneInfo.Local.StandardName}");

    // Dafny files to include
    foreach (string i in Includes) {
      res.AppendLine(String.Format("include \"{0}\"", i));
    }
    if (file.hasOwnership) {
      res.AppendLine("include \"ownershipInvariantsAutogen.dfy\"");
    }
    res.AppendLine();

    res.AppendLine("module ProofDraft {");
    res.AppendLine(PrintAsyncProofModuleBody(file, options));
    res.AppendLine("} // end module ProofDraft");
    return res.ToString();
  }

  private static string PrintAsyncProofModuleBody(AsyncProofFile file, DafnyOptions options) {
    var res = new StringBuilder();
    foreach (string i in Imports) {
      res.AppendLine(String.Format("  import opened {0}", i));
    }
    if (file.hasOwnership) {
      res.AppendLine("  import opened OwnershipInvariants");
    }
    res.AppendLine();

    // Print Application Invariant predicates
    foreach (Function appInv in file.GetAppInvPredicates()) {
      res.AppendLine(FormatInvariantPredicate(appInv, options));
    }

    // Print Application Invariant bundle
    res.Append(GetFromTemplate("ProtocolInvHeader", 0));
    foreach (Function appInv in file.GetAppInvPredicates()) {
      res.AppendLine("  && " + appInv.Name + "(c, v)");
    }
    if (file.GetAppInvPredicates().Count == 0) {
      res.AppendLine("  true");
    }
    res.AppendLine("}");
    res.AppendLine();

    // Print Inv bundle
    if (file.hasOwnership) {
      res.AppendLine(GetFromTemplate("InvWithOwnership", 0));
    } else {
      res.AppendLine(GetFromTemplate("Inv", 0));
    }

    // Print proof obligations
    res.AppendLine(GetFromTemplate("ObligationsSeparator", 0));
    res.AppendLine(GetFromTemplate("InvImpliesSafety", 0));
    if (file.hasOwnership) {
      res.AppendLine(GetFromTemplate("InitImpliesInvHeaderWithOwnership", 0));
    } else {
      res.AppendLine(GetFromTemplate("InitImpliesInv", 0));
    }
    
    // Print InvInductive proof body. Get directly from Sync
    res.AppendLine(FormatInvInductive(file.invInductiveLemma, file.hasOwnership, options));

    // Print InvNext Lemmas 
    if (file.GetInvNextLemmas().Count != 0) {
      res.AppendLine();
      res.AppendLine(GetFromTemplate("InvNextLemmasSeparator", 0));
      foreach (Lemma lemma in file.GetInvNextLemmas()) {
        // ignore sync-specific helper lemmas with incompatible signature
        if (SignatureIsAsyncCompatible(lemma)) {
          res.AppendLine(FormatInvNextLemma(file, lemma, options));
        }
      }
      if (file.hasOwnership) {
        res.AppendLine(FormatAtMostOwnerPerKeyImpliesSafety(file));
      }
    } else {
      if (file.hasOwnership) {
        res.AppendLine();
        res.AppendLine(GetFromTemplate("InvNextLemmasSeparator", 0));
        res.AppendLine(FormatAtMostOwnerPerKeyImpliesSafety(file));
      }
    }

    // Print helper lemmas
    if (file.GetHelperLemmas().Count != 0) {
      res.AppendLine();
      res.AppendLine(GetFromTemplate("HelperLemmasSeparator", 0));
      foreach (Lemma lemma in file.GetHelperLemmas()) {
        // ignore sync-specific helper lemmas with incompatible signature
        if (SignatureIsAsyncCompatible(lemma)) {
          res.AppendLine(FormatHelperLemma(file, lemma, options));
        }
      }
    }

    // Print helper functions
    if (file.GetHelperFunctions().Count != 0) {
      res.AppendLine();
      res.AppendLine(GetFromTemplate("HelperFunctionsSeparator", 0));
      foreach (Function f in file.GetHelperFunctions()) {
        res.AppendLine(FormatHelperFunction(f, options));
      }
    }

    // Print special helper functions
    if (file.GetSpecialHelperFunctions().Count != 0) {
      res.AppendLine();
      foreach (Function f in file.GetSpecialHelperFunctions()) {
        res.AppendLine(FormatSpecialHelperFunction(f, options));
      }
    }
    return res.ToString();
  } // end function PrintAsyncProofModuleBody 
  
  // Transform a sync predicate into async one
  private static string FormatInvariantPredicate(Function syncAppPred, DafnyOptions options) {
    var res = new StringBuilder();
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintFunction(syncAppPred, 0, false, 1);
    var pred = wr.ToString();

    pred = pred.Replace("History(i).WF(c)", "WF(c)");  // hacky

    // Format Kondo triggers
    string pattern = @"\{:trigger [^\}]*\}";
    var syncTriggers = Regex.Matches(pred, pattern).Cast<Match>().Select(match => match.Value).ToList();
    foreach (var st in syncTriggers) {
      pred = pred.Replace(st, TransformTrigger(st));
    }

    res.Append(pred);
    return res.ToString();
  }

  // Transform sync InvInductive lemma into async one
  private static string FormatInvInductive(Lemma syncInvInductive, bool ownership, DafnyOptions options) {
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintMethod(syncInvInductive, 0, false, 0);
    var invInductive = wr.ToString();
    // insert VariableNextProperties(c, v, v') into string
    int index = invInductive.IndexOf("{");
    if (ownership) {
      invInductive = invInductive.Insert(index+2, "  VariableNextProperties(c, v, v');\n  MonotonicityInvInductive(c, v, v');\n  MessageInvInductive(c, v, v');\n  OwnershipInvInductive(c, v, v');\n  AtMostOwnerPerKeyImpliesSafety(c, v');\n");
    } else {
      invInductive = invInductive.Insert(index+2, "  VariableNextProperties(c, v, v');\n  MonotonicityInvInductive(c, v, v');\n  MessageInvInductive(c, v, v');\n");
    }
    return invInductive;
  }

  // Transform a sync InvNext lemma into async one
  private static string FormatInvNextLemma(AsyncProofFile file, Lemma syncLemma, DafnyOptions options) {
    if (BodyIsAsyncCompatible(syncLemma, options)) {
      var wr = new StringWriter();
      var printer = new Printer(wr, options);
      printer.PrintMethod(syncLemma, 0, false, 1);
      var res = wr.ToString();
      // If Inv(c, v) requirement is missing, it means that specific AppInvs are used.
      // Insert Msg and Mono Invs
      if (!res.Contains("requires Inv(c, v)")) {
        var pattern = "requires v.WF(c)";
        var insertIdx = res.IndexOf(pattern) + pattern.Length + 1;
        res = res.Insert(insertIdx, "  requires MonotonicityInv(c, v)\n  requires MessageInv(c, v)\n");
      }

      // Don't use v.History(i) for AppInv calls
      foreach (Function f in file.GetAppInvPredicates()) {
        var pattern = @$"{f.Name}.*History\(i\)";  // match the entire lemma call
        var matches = Regex.Matches(res, pattern).Cast<Match>().Select(match => match.Value).ToList();
        foreach (string m in matches) {
          var replacement = m.Replace(".History(i)", "");
          res = res.Replace(m, replacement);
        }
      }
      return res.ToString();
    }
    return FormatSyncSpecificLemma(syncLemma, options);
  }

  // Identifies case 2 sync lemmas
  private static bool BodyIsAsyncCompatible(Lemma syncLemma, DafnyOptions options) {
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintMethod(syncLemma, 0, false, 0);
    var lemmaStr = wr.ToString();
    return !lemmaStr.Contains("sysStep");
  }

  // Identifies case 2 sync lemmas
  private static bool SignatureIsAsyncCompatible(Lemma syncLemma) {
    // Check if function signature has type Step argument
    foreach (var formal in syncLemma.Ins) {
      if (formal.Type is UserDefinedType && ((UserDefinedType)formal.Type).Name == "Step") {
        return false;
      }
    }
    return true;
  }

  // Format a case 2 sync lemma
  private static string FormatSyncSpecificLemma(Lemma syncLemma, DafnyOptions options) {
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintMethod(syncLemma, 0, true, 0);
    wr.WriteLine(GetFromTemplate("SyncSpecificLemma", 2));
    var res = wr.ToString();

    // Comment out lines with sync-Specific syntax
    string pattern = @"requires.*Step?|decreases.*Step";
    var synclines = Regex.Matches(res, pattern).Cast<Match>().Select(match => match.Value).ToList();
    foreach (var sl in synclines) {
      res = res.Replace(sl, "// " + sl);
    }
    return res.ToString();
  }

  // Transform sync helper lemma into async one
  private static string FormatHelperLemma(AsyncProofFile file, Lemma syncLemma, DafnyOptions options) {
    var res = "";
    if (BodyIsAsyncCompatible(syncLemma, options)) {
      var wr = new StringWriter();
      var printer = new Printer(wr, options);
      printer.PrintMethod(syncLemma, 0, false, 2);
      var linesList = wr.ToString().Split("\n").ToList();
      // hacky way to transform requires clauses, as I only wanna transform "v." and not "v"
      for (int i = 0; i < linesList.Count; i++) {
        if (linesList[i].Contains("decreases")) {
          break;
        } 
        linesList[i] = linesList[i].Replace("v.", "v.Last().");
        linesList[i] = linesList[i].Replace("v'.", "v'.Last().");
      }
      res = String.Join("\n", linesList);
      res = res.Replace("Last().WF(c)", "WF(c)");  // hacky
      res = res.Replace("Safety(c, v.Last())", "Safety(c, v)");  // hacky
      res = StripTriggerAnnotations(res);
    } else {
      res = FormatSyncSpecificLemma(syncLemma, options);
    }
    // Don't use v.Last() for Lemma calls
    foreach (Lemma l in file.GetHelperLemmas()) {
      var pattern = @$"{l.Name}\(.*Last\(\),";
      var matches = Regex.Matches(res, pattern).Cast<Match>().Select(match => match.Value).ToList();
      foreach (string m in matches) {
        var replacement = m.Replace(".Last()", "");
        res = res.Replace(m, replacement);
      }
    }

    // Use v.Last() for special predicate calls
    foreach (Function sp in file.GetSpecialHelperFunctions()) {
      var pattern = @$" {sp.Name}\(.*v,| {sp.Name}\(.*v',";
      var matches = Regex.Matches(res, pattern).Cast<Match>().Select(match => match.Value).ToList();
      foreach (string m in matches) {
        var replacement = m.Replace("v,", "v.Last(),");
        replacement = replacement.Replace("v',", "v'.Last(),");
        res = res.Replace(m, replacement);
      }
    }
    return res;
  }

  private static string FormatHelperFunction(Function function, DafnyOptions options) {
    foreach (Formal fm in function.Formals) {
      if (fm.Type.IsTopLevelTypeWithMembers && fm.Type.AsTopLevelTypeWithMembers.Name == "Variables") {
        // If takes (v: Variables) as argument, format as if Inv predicate
        return FormatInvariantPredicate(function, options);
      }
    }
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    printer.PrintFunction(function, 0, false, 0);
    return wr.ToString();
  }

  private static string FormatSpecialHelperFunction(Function function, DafnyOptions options) {
    var wr = new StringWriter();
    var printer = new Printer(wr, options);
    wr.WriteLine("// I am special");
    printer.PrintFunction(function, 0, false, 0);
    var res = wr.ToString();
    res = res.Replace("v: Variables", "v: Hosts");  // hacky
    return res;
  }

  private static string FormatAtMostOwnerPerKeyImpliesSafety(AsyncProofFile file) {
    var res = new StringBuilder();

    // Print lemma header
    res.Append(GetFromTemplate("AtMostOwnerPerKeyImpliesSafetyLemmaHeader", 0));
    foreach (var kvp in file.ExtractHosts()) {
      var mod = kvp.Key;
      res.AppendLine($"  requires AtMostOneOwnerPerKey{mod}(c, v)");
      res.AppendLine("  ensures Safety(c, v)");
    }
    res.AppendLine("{");

    // Print lemma body
    foreach (var kvp in file.ExtractHosts()) {
      var field = kvp.Value; var mod = kvp.Key;
      res.AppendLine("  forall idx1, idx2, k: UniqueKey |");
      res.AppendLine($"    && {ValidActorIdx("idx1", field)}");
      res.AppendLine($"    && {ValidActorIdx("idx2", field)}");
      res.AppendLine($"    && {mod}.HostOwnsUniqueKey(c.{field}[idx1], v.Last().{field}[idx1], k)");
      res.AppendLine($"    && {mod}.HostOwnsUniqueKey(c.{field}[idx2], v.Last().{field}[idx2], k)");
      res.AppendLine("  ensures idx1 == idx2");
      res.AppendLine("  {");
      res.AppendLine($"    assert {mod}.HostOwnsUniqueKey(c.{field}[idx1], v.Last().{field}[idx1], k);  // trigger");
      res.AppendLine("  }");
    }

    // Terminate
    res.AppendLine("}");
    return res.ToString();
  }

  // Transform sync trigger into corresponding async trigger
  private static string TransformTrigger(string trigger) {
    // add v.ValidHistoryIdx(i) if i not present
    var res = trigger;
    if (!res.Contains("History(i)")) {
      int indexToInsert = res.Length - 1;
      res = res.Insert(indexToInsert, ", v.ValidHistoryIdx(i)");
    }
    return res;
  }

  private static string StripTriggerAnnotations(string input) {
    // Define the pattern to remove
    string pattern = @"\{:trigger [^\}]*\}";
    // Use Regex.Replace to remove all occurrences of the pattern
    string resultString = Regex.Replace(input, pattern, "");
    return resultString;
  }

  private static string ValidActorIdx(string actor, string field) {
    return string.Format("0 <= {0} < |c.{1}|", actor, field);
  }
} // end class MessageInvariantsFile
} //end namespace Microsoft.Dafny