package eventb2javajml_plugin.machine;

import java.util.ArrayList;

import org.eventb.core.IPORoot;
import org.eventb.core.IPOSequent;
import org.eventb.core.IPSStatus;
import org.eventb.core.ISCAction;
import org.eventb.core.ISCEvent;
import org.eventb.core.ISCGuard;
import org.eventb.core.ISCInternalContext;
import org.eventb.core.ISCInvariant;
import org.eventb.core.ISCParameter;
import org.eventb.core.ISCRefinesEvent;
import org.eventb.core.ISCRefinesMachine;
import org.eventb.core.ISCVariable;
import org.eventb.core.ISCVariant;
import org.eventb.core.ISCWitness;
import org.eventb.core.basis.SCMachineRoot;
import org.eventb.core.pog.IPOGNature;
import org.eventb.internal.ui.prover.ProverUI;
import org.rodinp.core.IInternalElement;
import org.rodinp.core.IRodinElement;
import org.rodinp.core.IRodinFile;
import org.rodinp.core.IRodinProject;
import org.rodinp.core.RodinDBException;


public class MachineUtils {
	
	
	// it returns the name of the machine referenced by the editor
	public String fetchMachineName(ProverUI editorUI) {
		return editorUI.getUserSupport().getInput().getElementName();
	}
	
	// returns the list of contexts declared by machineName 
	// for the editor, rodinFile == editorUI.getRodinInputFile(), and machineName == fetchMachineName()
	// the result can be accessed as result[i].getRoot().getChildren() 
	public ISCInternalContext[] fetchMachineContexts(IRodinFile rodinFile, String machineName) throws RodinDBException {
		ArrayList<ISCInternalContext> result = new ArrayList<ISCInternalContext>();

		IRodinProject rodinProject = rodinFile.getRodinProject();
		IRodinElement[] rodinElements = rodinProject.getChildren();
		  		
		for(IRodinElement rodinElement : rodinElements) {
			 IInternalElement internalElement = ((IRodinFile)rodinElement).getRoot();
			 if(internalElement instanceof SCMachineRoot) {
				 SCMachineRoot machineRoot = (SCMachineRoot) internalElement;
				 if(machineName.equals(machineRoot.getElementName())) {
					 for(ISCInternalContext e : machineRoot.getChildrenOfType(ISCInternalContext.ELEMENT_TYPE)) {
						 result.add(e);
					 }
				 }
			 }
		}
		return (ISCInternalContext[]) result.toArray(new ISCInternalContext[result.size()]);
	}
	
	// returns the list of machines refined by machineName 
	// for the editor, rodinFile == editorUI.getRodinInputFile(), and machineName == fetchMachineName()
	// the result can be accessed as result[i].getRoot().getChildren() 
	public ISCRefinesMachine[] fetchRefinedMachines(IRodinFile rodinFile, String machineName) throws RodinDBException {
		ArrayList<ISCRefinesMachine> result = new ArrayList<ISCRefinesMachine>();

		IRodinProject rodinProject = rodinFile.getRodinProject();
		IRodinElement[] rodinElements = rodinProject.getChildren();
		  		
		for(IRodinElement rodinElement : rodinElements) {
			 IInternalElement internalElement = ((IRodinFile)rodinElement).getRoot();
			 if(internalElement instanceof SCMachineRoot) {
				 SCMachineRoot machineRoot = (SCMachineRoot) internalElement;
				 if(machineName.equals(machineRoot.getElementName())) {
					 for(ISCRefinesMachine e : machineRoot.getChildrenOfType(ISCRefinesMachine.ELEMENT_TYPE)) {
						 result.add(e);
					 }
				 }
			 }
		}
		return (ISCRefinesMachine[]) result.toArray(new ISCRefinesMachine[result.size()]);
	}	
	
	// it returns the invariants declared by machineName, which includes the invariants of the refined machine
	// for the editor, rodinFile == editorUI.getRodinInputFile(), and machineName == fetchMachineName()
	public ISCInvariant[] fetchInvariants(IRodinFile rodinFile, String machineName) throws RodinDBException {
		ArrayList<ISCInvariant> result = new ArrayList<ISCInvariant>();

		IRodinProject rodinProject = rodinFile.getRodinProject();
		IRodinElement[] rodinElements = rodinProject.getChildren();
		
		for(IRodinElement rodinElement : rodinElements) {
			 IInternalElement internalElement = ((IRodinFile)rodinElement).getRoot();
			 if(internalElement instanceof SCMachineRoot) {
				 SCMachineRoot machineRoot = (SCMachineRoot) internalElement;
				 if(machineRoot.getElementName().equals(machineName)) {
					 for(ISCInvariant e : machineRoot.getChildrenOfType(ISCInvariant.ELEMENT_TYPE)) {
						 if(!e.isTheorem())
							 result.add(e);
					 }
				 }
			 }
		}
		return (ISCInvariant[]) result.toArray(new ISCInvariant[result.size()]);
	}
	
	// it returns the theorems declared by machineName
	// for the editor, rodinFile == editorUI.getRodinInputFile(), and machineName == fetchMachineName();
	public ISCInvariant[] fetchMachineTheorems(IRodinFile rodinFile, String machineName) throws RodinDBException {
		ArrayList<ISCInvariant> result = new ArrayList<ISCInvariant>();

		IRodinProject rodinProject = rodinFile.getRodinProject();
		IRodinElement[] rodinElements = rodinProject.getChildren();
		
		for(IRodinElement rodinElement : rodinElements) {
			 IInternalElement internalElement = ((IRodinFile)rodinElement).getRoot();
			 if(internalElement instanceof SCMachineRoot) {
				 SCMachineRoot machineRoot = (SCMachineRoot) internalElement;
				 if(machineRoot.getElementName().equals(machineName)) {
					 for(ISCInvariant e : machineRoot.getChildrenOfType(ISCInvariant.ELEMENT_TYPE)) {
						 if(e.isTheorem())
							 result.add(e);
					 }
				 }
			 }
		}
		return (ISCInvariant[]) result.toArray(new ISCInvariant[result.size()]);
	}
	

	// it returns the variables declared by machineName (and the refined machines)
	// for the editor, rodinFile == editorUI.getRodinInputFile(), and machineName == fetchMachineName();
	public ISCVariable[] fetchMachineVariables(IRodinFile rodinFile, String machineName) throws RodinDBException {
		ArrayList<ISCVariable> result = new ArrayList<ISCVariable>();

		IRodinProject rodinProject = rodinFile.getRodinProject();
		IRodinElement[] rodinElements = rodinProject.getChildren();
		
		for(IRodinElement rodinElement : rodinElements) {
			 IInternalElement internalElement = ((IRodinFile)rodinElement).getRoot();
			 if(internalElement instanceof SCMachineRoot) {
				 SCMachineRoot machineRoot = (SCMachineRoot) internalElement;
				 if(machineName.equals(machineRoot.getElementName())) {
					 for(ISCVariable e : machineRoot.getChildrenOfType(ISCVariable.ELEMENT_TYPE)) {
						 result.add(e);
					 }
				 }
			 }
		}
		return (ISCVariable[]) result.toArray(new ISCVariable[result.size()]);
	}

	
	
	
	// it returns the variants of machineName
	// for the editor, rodinFile == editorUI.getRodinInputFile(), and machineName == fetchMachineName();
	public ISCVariant[] fetchVariants(IRodinFile rodinFile, String machineName) throws RodinDBException {
		ArrayList<ISCVariant> result = new ArrayList<ISCVariant>();

		IRodinProject rodinProject = rodinFile.getRodinProject();
		IRodinElement[] rodinElements = rodinProject.getChildren();
		
		for(IRodinElement rodinElement : rodinElements) {
			 IInternalElement internalElement = ((IRodinFile)rodinElement).getRoot();
			 if(internalElement instanceof SCMachineRoot) {
				 SCMachineRoot machineRoot = (SCMachineRoot) internalElement;
				 if(machineName.equals(machineRoot.getElementName())) {
					 for(ISCVariant e : machineRoot.getChildrenOfType(ISCVariant.ELEMENT_TYPE)) 
						 result.add(e);
				 }
			 }
		}
		return (ISCVariant[]) result.toArray(new ISCVariant[result.size()]);
	}
	
	// it returns the PO sequent referenced by the editor
	public IPSStatus fetchCurrentPO(ProverUI editorUI) {
		IPSStatus ps = editorUI.getCurrentProverSequent();
		//IPOSequent seq = ps.getPOSequent();
		
		return ps;
	}
	
	// it returns the proof-obligation sequent of the proof obligation named poName
	// for the editor, rodinFile == editorUI.getRodinInputFile(),  
	// machineName == fetchMachineName(), and poNmae == fetchCurrentPO().getElementName()
	public IPOSequent fetchPO(IRodinFile rodinFile, String machineName, String poName) throws RodinDBException {
		IRodinProject rodinProject = rodinFile.getRodinProject();
		IRodinElement[] rodinElements = rodinProject.getChildren();
				
		for(IRodinElement rodinElement : rodinElements) {
			
			IInternalElement internalElement = ((IRodinFile)rodinElement).getRoot();
            	 
			if (internalElement instanceof IPORoot) {		
				 IPORoot por = (IPORoot) internalElement;
				 
				 if(por.getElementName().equals(rodinFile.getBareName())) {
					 for(IRodinElement po : por.getChildren()) {
						 if(po.getElementName().equals(poName))
							 return ((IPOSequent)po);
					 }
				 }
			 }
		}
		return null;
	}
	
	// it returns the proof-status of all the proof obligations of nature the_nature in rodinFile.
	// for the editor, rodinFile == editorUI.getRodinInputFile()
	public IPSStatus[] fetchPOs(IRodinFile rodinFile, IPOGNature the_nature) throws RodinDBException {
		ArrayList<IPSStatus> result = new ArrayList<IPSStatus>();
		
		IInternalElement root = rodinFile.getRoot();
		IRodinElement[] rodinElements = root.getChildren();
		
		for(IRodinElement rodinElement : rodinElements) {
			IPSStatus ps = (IPSStatus) rodinElement;
			
			if(ps.getPOSequent().getPOGNature() == the_nature)
				result.add(ps);
		}
		return (IPSStatus[]) result.toArray(new IPSStatus[result.size()]);
	}
	
/***Methods regarding to Events***/
	
	// it returns the event of the machine 'machineName' 
	public ISCEvent[] fetchmachineEvents(IRodinFile rodinFile, String machineName) throws RodinDBException {
		IRodinProject rodinProject = rodinFile.getRodinProject();
		IRodinElement[] rodinElements = rodinProject.getChildren();
		for(IRodinElement rodinElement : rodinElements) {
			 IInternalElement internalElement = ((IRodinFile)rodinElement).getRoot();
			 if(internalElement instanceof SCMachineRoot) {
				 SCMachineRoot machineRoot = (SCMachineRoot) internalElement;
				 if(machineName.equals(machineRoot.getElementName())) {
					 return machineRoot.getChildrenOfType(ISCEvent.ELEMENT_TYPE);
				 }
			 }
		}
		return null;
	}
	
	// it returns the evtName event refines
	public ISCRefinesEvent[] fetchEvtRefines(ISCEvent evt) throws RodinDBException {
		return evt.getSCRefinesClauses(); 
	}
	
	// it returns the evtName event parameters. 
	public ISCParameter[] fetchEvtParameters(ISCEvent evt) throws RodinDBException {
		return evt.getSCParameters(); 
	}
	
	// it returns the evtName event guards. 
	public ISCGuard[] fetchEvtGuards(ISCEvent evt) throws RodinDBException {
		return evt.getSCGuards(); 
	}
	
	// it returns the evtName event witnesses. 
	public ISCWitness[] fetchEvtWitnesses(ISCEvent evt) throws RodinDBException {
		return evt.getSCWitnesses(); 
	}

	// it returns the evtName event actions. 
	public ISCAction[] fetchEvtActions(ISCEvent evt) throws RodinDBException {
		return evt.getSCActions();
	}


}
