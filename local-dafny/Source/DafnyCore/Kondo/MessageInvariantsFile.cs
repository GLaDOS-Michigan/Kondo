using System.Collections.Generic;

namespace Microsoft.Dafny
{
  public class MessageInvariantsFile {

    // List of invariants
    private List<SendInvariant> sendInvariants;
    private List<ReceiveInvariant> receiveInvariants;

    // Constructor
    public MessageInvariantsFile()
    {
      sendInvariants = new List<SendInvariant>{};
      receiveInvariants = new List<ReceiveInvariant>{};
    }

    public void AddSendInvariant(SendInvariant si) {
      sendInvariants.Add(si);
    }

    public void AddReceiveInvariant(ReceiveInvariant ri) {
      receiveInvariants.Add(ri);
    }

    public List<SendInvariant> GetSendInvariants() {
      return sendInvariants;
    }

    public List<ReceiveInvariant> GetReceiveInvariants() {
      return receiveInvariants;
    }

  } // end class MessageInvariantsFile
}