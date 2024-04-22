using System;
using System.Diagnostics;

namespace Microsoft.Dafny
{

  public class SendInvariant {

    private string functionName;  // name of the send predicate
    private string msgType;  // name of the type of message concerning this predicate
    private string module;   // name of the module this function belongs
    private string variableField;  // which field in distributedSystem.Hosts?

    public SendInvariant(string functionName, string msgType, string module, string variableField) {
      this.functionName = functionName;
      this.msgType = msgType;
      this.module = module;
      this.variableField = variableField;
    }

    public static SendInvariant FromFunction(Function sendPredicate, DatatypeDecl dsHosts) {
      // Extract module and msgType
      var module = ExtractSendInvariantModule(sendPredicate);
      var msgType = ExtractSendInvariantMsgType(sendPredicate);
      
      // extract field name in DistributedSystem.Hosts of type seq<[module].Variables>
      string variableField = null;
      foreach (var formal in dsHosts.GetGroundingCtor().Formals) {
        if (formal.DafnyName.Contains(string.Format("{0}.Variables", module))) {
          variableField = formal.CompileName;
          break;
        }
      }
      Debug.Assert(variableField != null, "variableField should not be null");
      Console.WriteLine(string.Format("Found send predicate [{0}] in module [{1}] for msg type [{2}], in Hosts.[{3}]\n", sendPredicate.Name, module, msgType, variableField));
    
      var sendInv = new SendInvariant(sendPredicate.Name, msgType, module, variableField);
      return sendInv;
    }

    // Message invariant function is of format "Send<MsgType>"
    private static string ExtractSendInvariantMsgType(Function func) {
      return func.Name.Substring(4);
    }

    // Get the Module in Module.SendPredicate
    private static string ExtractSendInvariantModule(Function func) {
      return func.FullDafnyName.Substring(0, func.FullDafnyName.IndexOf('.'));
    }
    
    public string GetName() {
      return this.functionName;
    }

    public string GetMessageType() {
      return msgType;
    }

    public string GetVariableField() {
      return variableField;
    }

    public string GetHostModule() {
      return module;
    }

    public string GetPredicateName() {
      return string.Format("{0}Validity", this.functionName);
    }

    public string GetLemmaName() {
      return string.Format("InvNext{0}Validity", this.functionName);
    }

    public string ToPredicate() {
      var res = string.Format("ghost predicate {0}(c: Constants, v: Variables)\n", GetPredicateName());
      res += "  requires v.WF(c)\n" +
             "  requires ValidMessages(c, v)\n" +
             "{\n" +
            string.Format("  forall msg | msg in v.network.sentMsgs && msg.{0}?\n", msgType) +
             "  ::\n" +
             "  (exists i ::\n" + 
             "    && v.ValidHistoryIdxStrict(i)\n" +
            string.Format("    && {0}.{1}(c.{2}[msg.Src()], v.History(i).{2}[msg.Src()], v.History(i+1).{2}[msg.Src()], msg)\n", module, functionName, variableField) +
             "  )\n" +
             "}\n";
      return res;
    }

    public string ToLemma() {
      var res = string.Format("lemma {0}(c: Constants, v: Variables, v': Variables)\n", GetLemmaName());
      res += "  requires v.WF(c)\n" +
             "  requires ValidMessages(c, v)\n" +
             string.Format("  requires {0}(c, v)\n", GetPredicateName()) +
             "  requires Next(c, v, v')\n" +
             string.Format("  ensures {0}(c, v')\n", GetPredicateName()) +
             "{\n" +
             string.Format("  forall msg | msg in v'.network.sentMsgs && msg.{0}?\n", msgType) +
             "  ensures\n" +
             "  (exists i ::\n" + 
             "    && v'.ValidHistoryIdxStrict(i)\n" +
            string.Format("    && {0}.{1}(c.{2}[msg.Src()], v'.History(i).{2}[msg.Src()], v'.History(i+1).{2}[msg.Src()], msg)\n", module, functionName, variableField) +
             "  ) {\n" +
             "    if msg !in v.network.sentMsgs {\n" + 
             "      // witness and trigger\n" +
             "      var i := |v.history|-1;\n" +
             string.Format("      assert {0}.{1}(c.{2}[msg.Src()], v'.History(i).{2}[msg.Src()], v'.History(i+1).{2}[msg.Src()], msg);\n", module, functionName, variableField) +
             "    }\n" +
             "  }\n" +
             "}\n";
      return res;
    }

    public override string ToString(){
      return string.Format("Send predicate [{0}] in module [{1}] for msg type [{2}], in DistributedSystem.[Hosts.{3}]", functionName, module, msgType, variableField);
    }  
  }
}