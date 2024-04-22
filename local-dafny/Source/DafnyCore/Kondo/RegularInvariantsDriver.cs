using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny
{
public class RegularInvariantsDriver {

  public DafnyOptions options;
  public Program program;
  public MessageInvariantsFile msgInvFile;
  public MonotonicityInvariantsFile monoInvFile;
  public OwnershipInvariantsFile ownerInvFile;

  // Constructor
  public RegularInvariantsDriver(DafnyOptions options, Program program)
  {
    this.options = options;
    this.program = program;
    msgInvFile = new MessageInvariantsFile();
    monoInvFile = new MonotonicityInvariantsFile();
    ownerInvFile = new OwnershipInvariantsFile();
  }

  public void Resolve() {
    Console.WriteLine(String.Format("Resolving invariants for {0}\n", program.FullName));

    // Find distributedSystem.Hosts
    DatatypeDecl dsHosts = null;
    foreach (var kvp in program.ModuleSigs) {
      foreach (var topLevelDecl in ModuleDefinition.AllTypesWithMembers(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
        if (topLevelDecl.FullDafnyName.Equals("DistributedSystem.Hosts")) {
          dsHosts = (DatatypeDecl) topLevelDecl;
          break;
        }
      }
    }
    Debug.Assert(dsHosts != null, "dsHosts should not be null");

    if (options.msgInvs) {
      ResolveMonotonicityInvariants(dsHosts, program);
      ResolveSendInvariants(dsHosts, program);
      ResolveReceiveInvariants(dsHosts, program);
    } 
    if (options.ownershipInvs) {
      ResolveOwnershipInvariants();
    }
  } // end method Resolve()

  private void ResolveOwnershipInvariants() {
    var systemModule = GetModule("DistributedSystem");

    // Find datatype Hosts
    IndDatatypeDecl hostsDecl = null;
    foreach (var decl in systemModule.TopLevelDecls.ToList()) {
      if (decl.Name.Equals("Hosts")) {
        ownerInvFile.AddHosts((IndDatatypeDecl) decl);
        hostsDecl = (IndDatatypeDecl) decl;
        break;
      }
    }
    Debug.Assert(hostsDecl != null, "hostsDecl should not be null");
  }

  private void ResolveMonotonicityInvariants(DatatypeDecl dsHosts, Program program) {
    foreach (var kvp in program.ModuleSigs) {
      var module = kvp.Value.ModuleDef;
      if (module.DafnyName.Contains("Host")) {

        // Find Variable type definition
        foreach (var decl in module.SourceDecls) {
          if (decl.Name.Equals("Variables")) {
            var monoInvs = MonotonicityInvariant.FromVariableDecl((DatatypeDecl) decl, dsHosts);
            foreach (var mi in monoInvs) {
              monoInvFile.AddInvariant(mi);
            }
            break;
          }
        }
      }
    }
  }

  private void ResolveSendInvariants(DatatypeDecl dsHosts, Program program) {
    // Find Send Predicate definitions
    var sendPredicateDefs = new List<Function>();
    foreach (var kvp in program.ModuleSigs) {
      foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
        if (topLevelDecl.Name.StartsWith("Send") && !topLevelDecl.FullDafnyName.StartsWith("Types.")) {  // identifying marker for Send Predicate
          sendPredicateDefs.Add(topLevelDecl);
        }
      }
    }

    // Create SendInvariant objects
    foreach (var sp in sendPredicateDefs) {   
      var sendInv = SendInvariant.FromFunction(sp, dsHosts);
      msgInvFile.AddSendInvariant(sendInv);
    }
  }

  private void ResolveReceiveInvariants(DatatypeDecl dsHosts, Program program) {
    // Find Receive Predicate trigger definitions
    // Trigger and Conclusion definitions
    var receivePredicateTriggers = new List<Function>();
    foreach (var kvp in program.ModuleSigs) {
      foreach (var topLevelDecl in ModuleDefinition.AllFunctions(kvp.Value.ModuleDef.TopLevelDecls.ToList())) {
        if (topLevelDecl.Name.StartsWith("Receive") && topLevelDecl.Name.Contains("Trigger"))  {  // identifying marker for Receive Predicate
          receivePredicateTriggers.Add(topLevelDecl);
        }
      }
    }

    // Create ReceiveInvariant objects
    foreach (var rpt in receivePredicateTriggers) {
      var recvInv = ReceiveInvariant.FromTriggerFunction(rpt, dsHosts);
      msgInvFile.AddReceiveInvariant(recvInv);
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

  public void WriteToFile() {
    if (options.msgInvs) {
      // Write monotonicity invariants
      string monoInvString = RegularInvPrinter.PrintMonotonicityInvariants(monoInvFile, program.FullName);
      string monoInvOutputFullname = Path.GetDirectoryName(program.FullName) + "/monotonicityInvariantsAutogen.dfy";
      Console.WriteLine(string.Format("Writing monotonicity invariants to {0}", monoInvOutputFullname));
      File.WriteAllText(monoInvOutputFullname, monoInvString);

      // Write message invariants
      string msgInvString = RegularInvPrinter.PrintMessageInvariants(msgInvFile, program.FullName);
      string msgInvOutputFullname = Path.GetDirectoryName(program.FullName) + "/messageInvariantsAutogen.dfy";
      Console.WriteLine(string.Format("Writing message invariants to {0}", msgInvOutputFullname));
      File.WriteAllText(msgInvOutputFullname, msgInvString);
    } 
    if (options.ownershipInvs) {
      // Write ownership invariants
      string ownerInvString = RegularInvPrinter.PrintOwnershipInvariants(ownerInvFile, program.FullName);
      string ownerInvOutputFullname = Path.GetDirectoryName(program.FullName) + "/ownershipInvariantsAutogen.dfy";
      Console.WriteLine(string.Format("Writing ownership invariants to {0}", ownerInvOutputFullname));
      File.WriteAllText(ownerInvOutputFullname, ownerInvString);
    }
  }
}  // end class MessageInvariantsDriver
} // end namespace Microsoft.Dafny