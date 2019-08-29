//TODO to delete everything related to LV
package eventb2javajml_plugin.machine;


import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

import org.eclipse.jface.dialogs.MessageDialog;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JTextArea;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IStatusLineManager;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorActionDelegate;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.eventb.core.EventBPlugin;
import org.eventb.core.IConvergenceElement.Convergence;
import org.eventb.core.ISCAction;
import org.eventb.core.ISCAxiom;
import org.eventb.core.ISCCarrierSet;
import org.eventb.core.ISCConstant;
import org.eventb.core.ISCEvent;
import org.eventb.core.ISCGuard;
import org.eventb.core.ISCInternalContext;
import org.eventb.core.ISCInvariant;
import org.eventb.core.ISCParameter;
import org.eventb.core.ISCRefinesEvent;
import org.eventb.core.ISCRefinesMachine;
import org.eventb.core.ISCVariable;
import org.eventb.core.ISCVariant;
import org.eventb.core.ast.FormulaFactory;
import org.eventb.ui.eventbeditor.IEventBEditor;
import org.rodinp.core.IRodinFile;

import com.google.inject.Guice;
import com.google.inject.Injector;
import com.google.inject.Stage;

import eventb2javajml_plugin.constraintsolver.ConstraintSolver;
import eventb2javajml_plugin.constraintsolver.GuiceConfig;
import eventb2javajml_plugin.constraintsolver.ProB;

public class EB2JavaJml implements IEditorActionDelegate{
	IEventBEditor<?> editor;
	JButton openButton, saveButton;
	JTextArea log;
	JFileChooser fc;
	Pred2JavaJml Pred2Java;
	MachineUtils utils = new MachineUtils();

	public boolean with_exception = true;

	//contains the variables to be assigned in each event 
	ArrayList<String> vars_mod;
	//contains all eb variables, constants, carrier sets, and parameters 
	ArrayList<String> all_variables = new ArrayList<String>();
	//contains just the constants in the eb model
	public HashMap<String,ArrayList<String>> constantsVars;

	//contains just the variables in the eb model
	public ArrayList<String> variablesModel;

	///used to create getter and mutator methods
	public HashMap<String,String> var_methods;

	HashMap<String,String> evts;

	public static String tab = "\t";

	/*threaded represents the type of translation the user wants to make
	 true -> Threaded Version
	 false -> Non-threaded Version
	 */
	private boolean threaded;

	public void setActiveEditor(IAction action, IEditorPart targetEditor) {
		if (targetEditor instanceof IEventBEditor)
			editor = (IEventBEditor<?>) targetEditor;
	}


	public void run(IAction action) {
		final IRodinFile rodinFile = getSelectedComponent();

		if (action.getId().equals("eventb2jml_plugin.machine.EB2Java_threaded")){
			threaded = true;
		}else{
			threaded = false;
		}
		String projectName = rodinFile.getParent().getElementName();
		if (threaded)
			projectName += "_multi_threaded";
		else
			projectName += "_sequential";
		String machineName = rodinFile.getBareName().toString();

		evts = new HashMap<String,String>();
		constantsVars = new HashMap<String,ArrayList<String>>();

		var_methods = new HashMap<String,String>();

		Pred2Java = new Pred2JavaJml();

		//Machine info
		try {
			String output_machine_head = "package " + projectName + ";\n\n" +
					"import eventb_prelude.*;\n"+
					"import Util.*;\n" +
					"//@ model import org.jmlspecs.models.JMLObjectSet;\n"+
					"import java.util.concurrent.locks.Lock;\n" + 
					"import java.util.concurrent.locks.ReentrantLock;\n\n"
					//TODO
					//+"/*BEGIN CUSTOMISATION: Importing Classes */\n"+
					//check if the user already defined his own importing classes
					//if so, to put it here
					//"/*END CUSTOMISATION: Importing Classes */\n\n"
					;


			String output_machine = ruleM(rodinFile,machineName, projectName);

			try {

				System.out.println(output_machine_head);
				System.out.println(output_machine);



				String filePath = rodinFile.getResource().getRawLocation().toString();
				filePath = filePath.replace(machineName + "." + rodinFile.getResource().getFileExtension(), "");

				//Create directories
				String main_dir;
				main_dir =filePath+"generated_java_"+projectName;
				String src_dir =main_dir+File.separator+"src";
				//String jars_dir =main_dir+File.separator+"jars";
				String bin_dir =main_dir+File.separator+"bin";

				String machine_dir =src_dir+File.separator+projectName;
				/*String events_dir =src_dir+File.separator+projectName+File.separator
						+"events";*/
				String util_dir =src_dir+File.separator+"Util";

				String prelude_dir = src_dir+File.separator+"eventb_prelude";


				(new File(main_dir)).mkdir();
				(new File(src_dir)).mkdir();
				//(new File(jars_dir)).mkdir();
				(new File(bin_dir)).mkdir();
				(new File(machine_dir)).mkdir();
				//(new File(events_dir)).mkdir();
				(new File(util_dir)).mkdir();
				(new File(prelude_dir)).mkdir();

				//Files for the prelude 
				create_prelude(prelude_dir);

				//file for the eclipse project
				//1. .settings folder
				String settings_dir = main_dir+File.separator+".settings";

				(new File(settings_dir)).mkdir();

				//2. org.eclipse.jdt.core.prefs file
				FileWriter fstream_set = new FileWriter(main_dir+File.separator+".settings/org.eclipse.jdt.core.prefs");
				BufferedWriter out_set = new BufferedWriter(fstream_set);
				out_set.write("eclipse.preferences.version=1\n" +
						"org.eclipse.jdt.core.compiler.codegen.inlineJsrBytecode=enabled\n" +
						"org.eclipse.jdt.core.compiler.codegen.targetPlatform=1.6\n" +
						"org.eclipse.jdt.core.compiler.codegen.unusedLocal=preserve\n" +
						"org.eclipse.jdt.core.compiler.compliance=1.6\n" +
						"org.eclipse.jdt.core.compiler.debug.lineNumber=generate\n" +
						"org.eclipse.jdt.core.compiler.debug.localVariable=generate\n" +
						"org.eclipse.jdt.core.compiler.debug.sourceFile=generate\n" +
						"org.eclipse.jdt.core.compiler.problem.assertIdentifier=error\n" +
						"org.eclipse.jdt.core.compiler.problem.enumIdentifier=error\n" +
						"org.eclipse.jdt.core.compiler.source=1.6\n");
				out_set.close();
				fstream_set.close();

				//3. .classpath file
				FileWriter fstream_cp = new FileWriter(main_dir+File.separator+".classpath");
				BufferedWriter out_cp = new BufferedWriter(fstream_cp);
				out_cp.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" +
						"<classpath>\n" +
						"<classpathentry kind=\"src\" path=\"src\"/>\n" +
						"<classpathentry kind=\"con\" path=\"" +
						"org.eclipse.jdt.launching.JRE_CONTAINER/org.eclipse.jdt.internal.debug.ui.launcher.StandardVMType/JavaSE-1.6\"/>\n" +
						"</classpath>\n");
				out_cp.close();
				fstream_cp.close();

				//3. .project file
				FileWriter fstream_project = new FileWriter(main_dir+File.separator+".project");
				BufferedWriter out_project = new BufferedWriter(fstream_project);
				out_project.write("<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" +
						"<projectDescription>\n" +
						"<name>"+"generated_java_"+projectName+"</name>\n" +
						"<comment></comment>\n" +
						"<projects>\n" +
						"</projects>\n" +
						"<buildSpec>\n" +
						tab + "<buildCommand>\n" +
						tab + tab + "<name>org.eclipse.jdt.core.javabuilder</name>\n" +
						tab + tab + tab + "<arguments>\n" +
						tab + tab + tab + "</arguments>\n" +
						tab + "</buildCommand>\n" +
						tab + "</buildSpec>\n" +
						tab + "<natures>\n" +
						"<nature>org.eclipse.jdt.core.javanature</nature>\n" +
						"</natures>\n" +
						"</projectDescription>\n");
				out_project.close();
				fstream_project.close();

				//Utilities.java
				FileWriter fstream_util = new FileWriter(util_dir+File.separator+"Utilities.java");
				BufferedWriter out_util = new BufferedWriter(fstream_util);
				out_util.write(utilityFile());
				out_util.close();
				fstream_util.close();

				//machine_machineName.java 
				String fileName = machineName + ".java";

				customised_code(machine_dir, fileName, 1);

				FileWriter fstream_machine = new FileWriter(machine_dir+File.separator+fileName);
				BufferedWriter out_machine = new BufferedWriter(fstream_machine);
				out_machine.write(output_machine_head);
				out_machine.write(output_machine);
				out_machine.close();
				fstream_machine.close();
				ArrayList<String> name_evts = new ArrayList<String>(); 
				//events files
				for (String evt_name: evts.keySet()){
					String evt = evt_name + ".java";
					name_evts.add(evt_name);
					//machine_dirFileWriter fstream_evt = new FileWriter(events_dir+File.separator+evt);
					FileWriter fstream_evt = new FileWriter(machine_dir+File.separator+evt);
					BufferedWriter out_evt = new BufferedWriter(fstream_evt);
					System.out.println(evts.get(evt_name));
					out_evt.write(evts.get(evt_name));
					out_evt.close();
					fstream_evt.close();
				}

				//test_machineName.java 
				String test_fileName = "Test_" + machineName + ".java";

				FileWriter fstream_test_machine = new FileWriter(machine_dir+File.separator+test_fileName);
				BufferedWriter out_test_machine = new BufferedWriter(fstream_test_machine);
				try {
					out_test_machine.write(testFile("Test_" + machineName, machineName,projectName, name_evts));
				} catch (Exception e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}

				out_test_machine.close();
				fstream_test_machine.close();


				//displayInStatusBar("Successful translation", false);
				MessageDialog.openInformation(
						PlatformUI.getWorkbench().
						getActiveWorkbenchWindow().getShell(),
						"Success",
						"Successful Translation.\nCheck directory " + main_dir
						+ " which is available in the Resource perspective.");

			} catch (IOException e) {
				e.printStackTrace();
				//displayInStatusBar("Unsuccessful translation", false);
				MessageDialog.openInformation(
						PlatformUI.getWorkbench().
						getActiveWorkbenchWindow().getShell(),
						"Unsuccess",
						"Unsuccessful translation.");
				System.out.println("IOException 1: " + e.toString());
			}
		} catch (CoreException e) {
			e.printStackTrace();
			//displayInStatusBar("Unsuccessful translation", false);
			MessageDialog.openInformation(
					PlatformUI.getWorkbench().
					getActiveWorkbenchWindow().getShell(),
					"Unsuccess",
					"Unsuccessful translation.");
			System.out.println("IOException 2: " + e.toString());
		}
	}

	// Returns the abstract machine 'machineName' in eventB to JML
	public String ruleM(IRodinFile rodinFile, String machineName, String packageName) throws CoreException {

		all_variables = new ArrayList<String>();
		variablesModel = new ArrayList<String>();

		String res = "";
		PrintTrace("Starting the translation");
		PrintTrace("1. Sees");
		//Sees returns an ArrayList of an arrayList that contains:
		//		1. Sets
		//      2. Constants
		//      3. Axioms
		ArrayList<ArrayList<String>> sees = Sees(rodinFile, machineName);

		String S = ""; //Sets
		String C = ""; //Constants
		String X = ""; //Axioms

		for (ArrayList<String> ctx: sees){
			S += ctx.get(0);
			C += ctx.get(1);
			X += ctx.get(2);
		}

		// machineVariables method gets all variables name, the type
		// is translated using the type provided by EventB.
		PrintTrace("2. Variables");
		String V = machineVariables(rodinFile, machineName);

		//Pred2Java.PrintVarT2(Pred2Java.varType);
		PrintTrace("3. Invariants");
		String I = machineInvariants(rodinFile, machineName);

		PrintTrace("4. Events");
		//Init
		ArrayList<String> init = eventsInit(rodinFile, machineName);
		String I1 = "", I2 = "";
		if (init.size() != 0){
			I1 = init.get(0);
			I2 = init.get(1);
		}

		//String events = events(rodinFile, machineName);

		//Events
		//	evt_name: translation Java+Jml

		String variant = machineVariants(rodinFile, machineName).replaceAll("\\bmachine.\\b", "");
		String Va = "";
		if (!variant.equals("")){
			Va = 
					tab + "/*@ public normal_behavior\n"+
							tab + tab + "requires true;\n" +
							tab + tab + "assignable \\nothing;\n" +
							tab + tab + "ensures \\result == " + variant + ".intValue(); */\n" +
							tab + "public /*@ pure */ int variant(){\n" +
							tab + tab + "return " + variant + ".intValue();\n" +
							tab + "}\n\n";
		}
		
		evts = events(rodinFile, machineName, packageName);

		String GetSetMethods = create_getter_setter_methods();

		String E = "";
		ArrayList<String> evt_names = new ArrayList<String>(); //To change
		for (String evt: evts.keySet()){
			evt_names.add(evt);
			E += evts.get(evt);
		}

		String threadCreation = ThreadCreation(evt_names);
		res +=
				"public class " + machineName + "{\n";
		if (threaded){
			res +=	tab + "private int n_events = "+evt_names.size()+";\n";
		}
		res +=	tab + "private static final Integer max_integer = Utilities.max_integer;\n" +
				tab + "private static final Integer min_integer = Utilities.min_integer;\n";
		if (threaded){
			res += tab + "private Thread[] events;\n"+
					tab + "public Lock lock = new ReentrantLock(true);\n";
		}else{
			res += "\n" + ClassCreation(evt_names);
		}

		res +=	"\n\n" + 
				tab + "/******Set definitions******/\n" + 
				S + "\n" +
				tab + "/******Constant definitions******/\n" + 
				C + "\n\n" +
				tab + "/******Axiom definitions******/\n" + 
				X + "\n\n" +
				tab + "/******Variable definitions******/\n" +
				V + "\n\n" +

				Va + "\n" + 

				tab + "/******Invariant definition******/\n" +
				I + "\n\n" +
				tab + "/******Getter and Mutator methods definition******/\n" +
				GetSetMethods + "\n\n" +
				//TODO
				//tab + "/*BEGIN CUSTOMISATION */\n" +
				//tab + "/*END CUSTOMISATION */\n\n" +
				tab + "/*@ public normal_behavior\n" +
				tab + "    requires true;\n" + 
				tab + "    assignable \\everything;\n" + 
				tab + "    ensures\n" + I1 + "*/\n" +
				tab + "public " + machineName + "(){\n";

		res +=	I2 +"\n";
		if (threaded){
			res += threadCreation + "\n"; 
		}

		res += //TODO
				//tab+ tab + "/*BEGIN CUSTOMISATION */\n" +
				//tab + tab + "/*END CUSTOMISATION */\n\n"+

				tab + "}\n" + 
				"}";

		return res;
	}


	// Returns all machine 'machineName' 's specifications in EventB to JML
	public ArrayList<String> eventsInit(IRodinFile rodinFile, String machineName) throws CoreException, CoreException {
		ISCEvent[] evts = utils.fetchmachineEvents(rodinFile, machineName);
		ArrayList<String> res = new ArrayList<String>();
		for (ISCEvent evt : evts){
			PrintTrace("Event: " + evt.getLabel());
			if (evt.getLabel().equals("INITIALISATION")){
				return Init1_Init2Rule(evt);
			}
		}
		return res;
	}

	//Returns an ArrayString where the first element corresponds to the specification in JML
	//of the initially event in EventB. The second element corresponds to the translation to Java
	public ArrayList<String> Init1_Init2Rule(ISCEvent initEvt) throws CoreException, CoreException{
		ISCAction[] evtActions =  utils.fetchEvtActions(initEvt);
		ArrayList<String> res = new ArrayList<String>();
		int num_actions = evtActions.length;
		if (num_actions == 0){
			return res;
		}

		String init_jml = "";
		String init_java = "";
		for (ISCAction evtAction : evtActions){

			//translationTrace(evtAction.getLabel(),"act3");

			Pred2Java.member_of = true;
			HashMap<String, ArrayList<String>> tmp = transAssig(evtAction.getAssignmentString());
			Pred2Java.member_of = false;

			int i2 = tmp.size();
			for (String var : tmp.keySet()){
				if (tmp.get(var).get(0).equals("EMPTY")){
					init_jml += tab + tab + var + ".isEmpty()";
					init_java += tab + tab +var + " = new "+ getJmlType(var) +"();\n";
				}else if (tmp.get(var).get(0).equals("SET")){
					init_jml += tab + tab + var + ".equals(" + tmp.get(var).get(1).replaceAll("machine.", "") + ")";
					//init_java += tab + tab + var + " = new "+ getJmlType(var).replaceAll("machine.", "") +"(); \n";
					init_java += tab + tab + var + " = ("+ tmp.get(var).get(1).replaceAll("machine.", "") + ");\n";
				}else if (tmp.get(var).get(0).equals("NATIVE")){
					init_jml += tab + tab +  var + " == " + tmp.get(var).get(1).replaceAll("machine.", "");
					init_java += tab + tab + var + " = " + tmp.get(var).get(1).replaceAll("machine.", "") + ";\n";
				}else if (tmp.get(var).get(0).equals("NONDET")){
					init_jml += tab + tab + tmp.get(var).get(1).replaceAll("machine.", "");
					String predicate = tmp.get(var).get(3).replaceAll("tmp_", "");
					for (String non_det_var: tmp.get(var).get(2).split(",")){
						init_java += tab + tab + "//" +non_det_var + " = Utilities.non_det_assignment(" + 
								non_det_var + ",(" + 
								predicate + "));\n";
					}
				}else{ //BECOMES
					init_jml += tab + tab + tmp.get(var).get(1).replaceAll("machine.", "");
					String t_becomes = Pred2Java.transBecomes;

					String initValue = "";

					if (t_becomes.contains(".instance")){
						if (t_becomes.contains("BOOL.instance")){
							initValue = t_becomes.replace("BOOL.instance","BOOL.instance");
						}else if (t_becomes.contains("INT.instance")){
							initValue = t_becomes.replace("INT.instance","new Enumerated(min_integer, max_integer)");
						}else if (t_becomes.contains("NAT.instance")){
							initValue = t_becomes.replace("NAT.instance", "new Enumerated(0, max_integer)");
						}else{ // it is a NAT1.instance
							initValue = t_becomes.replace("NAT1.instance", "new Enumerated(1, max_integer)");
						}
					}else{
						if (t_becomes.equals("Integer")){
							initValue = "new Enumerated(min_integer, max_integer)";
						}else{
							initValue = t_becomes;
						}
					}
					init_java += tab + tab + var + " = Utilities.someVal("+ initValue.replaceAll("machine.", "") +");\n";

				}
				if (i2 > 1){
					init_jml += " &&\n";
				}i2--;
			}
			if (num_actions > 1){
				init_jml += " &&\n";
			}num_actions--;
		}
		init_jml += ";";

		res.add(init_jml);
		res.add(init_java);
		return res;
	}


	/*** Contexts seen***/

	public String ConstType(ISCConstant constant) throws CoreException{
		final FormulaFactory f = FormulaFactory.getDefault();
		//TODO: is missing when the type is a carry set

		
		String constantType = getType(constant.getElementName(), constant.getType(f).toString());

		return constantType;
		
	}

	// it transforms a constant declaration in B into JML
	// --> static final T c; where c is the constant and T its type.
	public String Constant(ISCConstant constant,String machineName) throws CoreException {
		String constantName = constant.getIdentifierString();
		PrintTrace("1. Sees \n\t 1.2. Constant " + constantName);
		String constantType =  ConstType(constant);		
		String internal_type = getInternalType(constantName);
		all_variables.add(constantName);
		ArrayList<String> type_consts = new ArrayList<String>();
		type_consts.add(constantType);
		type_consts.add(internal_type);
		constantsVars.put(constantName, type_consts);
		String suggestion = "";


		suggestion = "Test_" + machineName + ".random_" + constantName;
		String res = tab + "//@ public static constraint " + constantName + ".equals(\\old(" + constantName + ")); \n" + 
				tab + "public static final " + constantType + " " + constantName + " = "+ suggestion +";\n";

		return res +"\n";
	}

	// it transforms a list of constant declarations in B into JML
	public String ConsRule(ISCConstant[] constants, String machineName) throws CoreException {
		StringBuffer res = new StringBuffer("");

		for(ISCConstant constant: constants)
			res.append(Constant(constant,machineName));

		return res.toString();
	}

	// it transforms an axiom in B into JML
	public String Axiom(ISCAxiom axiom, boolean theorem) throws CoreException {
		String res = "";
		PrintTrace("1. Sees \n\t 1.3. Axiom " + axiom.getLabel());
		if (!theorem){
			//translationTrace(axiom.getLabel(), "axm6");
			res = tab + "/*@ public static invariant "+ transPred(axiom.getPredicateString(),false).replaceAll("machine.", "")+"; */";
			//res = tab + "/*@ public invariant "+ transPred(axiom.getPredicateString(),false).replaceAll("machine.", "")+"; */";
		}else
			res = tab + "/*@ public static invariant_redundantly "+ transPred(axiom.getPredicateString(),false).replaceAll("machine.", "")+"; */";
		//res = tab + "/*@ public invariant_redundantly "+ transPred(axiom.getPredicateString(),false).replaceAll("machine.", "")+"; */";
		return res +"\n";
		//return "\n";
	}

	// it transforms a list of axioms in B into JML
	public String AxiomRule(ISCAxiom[] axioms) throws CoreException {
		StringBuffer res = new StringBuffer("");

		for(ISCAxiom axiom : axioms){
			res.append(Axiom(axiom,axiom.isTheorem()));
		}
		return res.toString();
	}

	// it transforms a carrier set definition in B into JML
	// model JMLEqualsSet<Integer> s; where s is the set
	public String Set(ISCCarrierSet set) throws CoreException {
		String resvar = set.getElementName(); 
		//TODO: According with the type the translation changes
		//	See: Set and Enum rule definitions
		//TODO: How to specify that using BSet?
		//String restype = SetType(set);
		PrintTrace("1. Sees \n\t 1.1. Set " + resvar);

		Pred2Java.setVarTypeSet(resvar);
		all_variables.add(resvar);
		//return "    /*@ public model BSet<Integer> " + resvar +";\n" +
		//		"     public constraint " + resvar + ".equals(\\old(" + resvar + ")); */\n" +
		//		"    public static final BSet<Integer> " + resvar + " = new BSet<Integer>(" +
		//				"new Enumerated(Integer.MIN_VALUE,Integer.MAX_VALUE));\n\n";*/

		return tab + "//@ public static constraint " + resvar + ".equals(\\old(" + resvar + ")); \n" +
		tab + "public static final BSet<Integer> " + resvar + " = new Enumerated(min_integer,max_integer);\n\n";
	}

	// it transforms a list of carrier set declarations in B into JML
	public String SetRule(ISCCarrierSet[] sets) throws CoreException {
		StringBuffer res = new StringBuffer("");

		for(ISCCarrierSet set: sets)
			res.append(Set(set));

		return res.toString();
	}

	// it transforms a machine context in B into JML
	public ArrayList<String> See(ISCInternalContext see, String machineName) throws CoreException {
		ArrayList<String> res = new ArrayList<String>();

		// sets
		ISCCarrierSet[] sets = see.getChildrenOfType(ISCCarrierSet.ELEMENT_TYPE);
		// constants
		ISCConstant[] constants = see.getChildrenOfType(ISCConstant.ELEMENT_TYPE);
		// axioms
		ISCAxiom[] axioms = see.getChildrenOfType(ISCAxiom.ELEMENT_TYPE);

		res.add(SetRule(sets));
		res.add(ConsRule(constants, machineName));
		res.add(AxiomRule(axioms));

		return res;
	}

	// it transforms a list of contexts in B into JML
	public ArrayList<ArrayList<String>> Sees(IRodinFile rodinFile, String machineName) throws CoreException {
		ISCInternalContext[] sees = utils.fetchMachineContexts(rodinFile,machineName);
		constantsVars = new HashMap<String,ArrayList<String>>();
		ArrayList<ArrayList<String>> res = new ArrayList<ArrayList<String>>();
		for(ISCInternalContext see : sees)
			res.add(See(see, machineName));

		return res;
	}

	/************************************************************************************************************/

	/*** for non-threaded version ***/
	String initialisation_params = ""; 
	String framework_guard_while = "";
	String framework_body_while = "";
	String new_value_params = "";
	/*** for non-threaded version ***/

	//returns the information of the events
	//key: event_name
	//value: the translation from event-B to Java code
	public HashMap<String,String> events(IRodinFile rodinFile, String machineName, 
			String packageName) throws CoreException {
		HashMap<String,String> res = new HashMap<String,String>();
		ISCEvent[] evts = utils.fetchmachineEvents(rodinFile, machineName);
		int n_events = evts.length - 1; //Initialisation event does not account
		int evt_number = 0;
		/*** for non-threaded version ***/
		initialisation_params = ""; 
		framework_guard_while = "";
		framework_body_while = "";
		new_value_params = "";
		/*** for non-threaded version ***/
		for (ISCEvent evt : evts){
			//evt.getCo
			if (!evt.getLabel().equals("INITIALISATION")){
				PrintTrace("Event: " + evt.getLabel());
				String translation = "";
				LinkedHashMap<String,String> par = eventParameters(evt);
				translation = ruleMethod(evt, par, machineName, packageName, n_events, evt_number);

				//parameters type must be removed since it is possible that another event
				//is using the same param name.
				for (String p: par.keySet()){
					if (Pred2Java.varType.containsKey(p)){
						Pred2Java.varType.remove(p);
					}
				}
				res.put(evt.getLabel(), translation);
				evt_number++;
			}
		}
		return res;
	}

	public String non_det_guard;
	//ruleMethod returns the Java code for the translation of an Event-B event to Java code
	//it also creates the corresponding creation of the events (also everything related to 
	//the parameters creation and initialisation)
	public String ruleMethod(ISCEvent evt, LinkedHashMap<String,String> parameters,String machineName, 
			String packageName, int n_events, int evt_number) throws CoreException {

		String evtName = evt.getLabel();

		String jml_guard = "";
		String jml_actions = "";

		LinkedHashMap<String, String> anyParameters = new LinkedHashMap<String, String>();

		for (String p : parameters.keySet()){

			all_variables.add(p);
			anyParameters.put(p,parameters.get(p));

		}

		ArrayList<String> Guards = eventGuards(evt);
		String G_jml = Guards.get(0);
		String G_java = Guards.get(1);

		non_det_guard = "";
		ArrayList<String> actions = eventActions(evt);
		
		String S = actions.get(0);
		String assg_java = actions.get(1);
		if (G_jml.equals("")){
			G_jml = "true";
			G_java = "true";
		}if (S.equals("")){
			S = "true";
		}

		String init_params_non_threaded = "";
		String init_params_threaded = "";
		String new_val_prs = "";
		String prints = tab + tab + tab +"System.out.println(\""+evtName+ " executed ";
		for (String p : parameters.keySet()){
			prints += p + ": \"" + " + "+p+" + \" ";
			G_jml = G_jml.replaceAll("\\bmachine." + p+"\\b", p);
			G_java = G_java.replaceAll("\\bmachine." + p+"\\b", p);
			S = S.replaceAll("\\bmachine." + p+"\\b", p);
			assg_java = assg_java.replaceAll("\\bmachine." + p+"\\b", p);
			String prs = any_parameter_initialisation(p, Pred2Java.varType.get(p));
			init_params_non_threaded += tab + tab + Pred2Java.varType.get(p).getJmlType() + " " + prs;
			init_params_threaded += tab + tab + tab + Pred2Java.varType.get(p).getJmlType() + " " + prs;
			new_val_prs += tab + tab + tab + prs;
		}

		prints += "\");\n";
		
		jml_guard += "/*@ public normal_behavior\n";
		
		jml_guard += tab + tab + "requires true;\n " +
				tab + tab +"assignable \\nothing;\n";

		//change machine.var to machine.get_var() in G_jml and G_java and S
		for (String varName: variablesModel){
			G_jml = G_jml.replaceAll("\\bmachine." + varName+"\\b", "machine.get_" + varName + "()");
			G_java = G_java.replaceAll("\\bmachine." + varName+"\\b", "machine.get_" + varName + "()");
			S = S.replaceAll("\\bmachine." + varName+"\\b", "machine.get_" + varName + "()");
		}
		
		if (evt.getConvergence().equals(Convergence.CONVERGENT) ||
				evt.getConvergence().equals(Convergence.ANTICIPATED)){
			G_jml += " && (machine.variant() >= 0)";
			G_java += " && (machine.variant() >= 0)";
		}
		

		if (non_det_guard.equals("")){
			jml_guard += tab + tab +"ensures \\result <==> " + G_jml + "; */";
		}else{
			jml_guard += tab + tab +"ensures (\\result <==> " + G_jml + 
					") && "+ non_det_guard.substring(0, non_det_guard.length()-4) +"; */";
		}

		//Variable vars is filled up when the method eventActions is called.
		String assig = "";
		int i = vars_mod.size();
		if (i == 0)
			assig = "\\nothing";
		else
			for (String v : vars_mod){
				assig += "machine."+v;
				if (i > 1){
					assig += ", ";
				}i--;
			}

		String ps = "";
		String ps_types = "";
		String init_ps = "";
		for (String param_name : anyParameters.keySet()){
			ps += param_name + ",";
			ps_types += " " + anyParameters.get(param_name) + " " + param_name + ",";
			init_ps += tab + tab + tab + anyParameters.get(param_name) + " " + param_name + " = null;" +
					" //non-deterministic assignment according to the guards\n";
		}
		if (ps.length() != 0){
			ps = ps.substring(0, ps.length()-1);
			ps_types = ps_types.substring(0, ps_types.length()-1);
		}

		String init_prs = ""; //for non-threaded version
		String guard_while = ""; //for non-threaded version
		String body_while = ""; //for non-threaded version
		//If the framework for non-threaded version is needed
		if (!threaded){
			if (!init_params_non_threaded.equals("")){
				initialisation_params += tab + tab + "//Init values for parameters in event: " + evtName + "\n" + 
						init_params_non_threaded + "\n";
			}
			framework_guard_while += tab + tab + tab + "  machine.evt_" + evtName + ".guard_" + evtName + "("+ps+")";

			if (evt_number+1 == n_events){
				framework_guard_while += "){\n";
			}else{
				framework_guard_while += " ||\n";
			}
			framework_body_while += tab + tab + tab + "case " + evt_number + ":" +
					" if (machine.evt_" + evtName + ".guard_" + evtName + "("+ps+"))\n" +
					tab + tab + tab + tab + "machine.evt_" + evtName + ".run_" + evtName + "("+ps+"); break;\n";
		}


		jml_actions += "/*@ public normal_behavior\n";
		
		jml_actions += tab + tab + "requires guard_"+evtName+"("+ps+");\n";
		jml_actions += tab + tab +"assignable " + assig + ";\n";
		jml_actions += tab + tab +"ensures guard_"+evtName+"("+ps+") && " + S;
		if (evt.getConvergence().equals(Convergence.CONVERGENT))
			jml_actions += "\n" + tab + tab + tab + " && machine.variant() < \\old(machine.variant())";
		else if (evt.getConvergence().equals(Convergence.ANTICIPATED))
			jml_actions += "\n" + tab + tab + tab + " && machine.variant() <= \\old(machine.variant())";

		jml_actions += "; \n";

		jml_actions += tab + " also\n";
		jml_actions += tab + tab +"requires !guard_"+evtName+"("+ps+");\n";
		jml_actions += tab + tab +"assignable \\nothing;\n";
		jml_actions += tab + tab +"ensures true; */";



		String res = "package "+packageName+"; \n\n"+
				"import eventb_prelude.*;\n"+
				"import Util.Utilities;\n\n"
				//TODO
				//+"/*BEGIN CUSTOMISATION: Importing Classes */\n" +
				//"/*END CUSTOMISATION: Importing Classes */\n\n"
				;
		if (threaded){
			res += "public class " + evtName + " extends Thread{\n";
		}else{
			res += "public class " + evtName + "{\n";
		}

		res +=	tab + "/*@ spec_public */ private " +machineName + " machine; // reference to the machine \n\n";

		//TODO
		//tab + "/*BEGIN CUSTOMISATION */\n"+
		//tab + "/*END CUSTOMISATION */\n\n" +
		res += 		tab + "/*@ public normal_behavior\n"+
				tab + tab + "requires true;\n" +
				tab + tab + "assignable \\everything;\n"+
				tab + tab + "ensures this.machine == m; */\n" +
				tab + "public " + evtName + "(" + machineName + " m) {\n"+
				tab + tab + "this.machine = m;\n";

		res +=	//TODO
				//"\n" + tab + tab + "/*BEGIN CUSTOMISATION */\n"+
				//tab + tab + "/*END CUSTOMISATION */\n\n" +
				tab + "}\n\n" +

				tab + jml_guard + "\n";
		
		res +=	tab + "public /*@ pure */ boolean guard_"+evtName+"("+ps_types+") {\n";
		
		res +=	//TODO
				//"\n" + tab + tab + "/*BEGIN CUSTOMISATION */\n"+
				//tab + tab + "/*END CUSTOMISATION */\n\n" +
				tab + tab + "return "+ G_java +";\n" +
				tab + "}\n\n"+

				tab + jml_actions +"\n";
		
		res += tab + "public void run_" + evtName + "("+ps_types+"){\n";
		
		res +=	//TODO
				//"\n" + tab + tab + "/*BEGIN CUSTOMISATION */\n"+
				//tab + tab + "/*END CUSTOMISATION */\n\n" +
				tab + tab + "if(guard_"+evtName+"("+ps+")) {\n" +
				assg_java +"\n" + 
				/* Just for tests */
				prints + 
				/* Just for tests */
				tab + tab + "}\n" + 
				tab + "}\n\n";
		if (threaded){
			res += tab + "public void run() {\n" +
					tab + tab + "while(true) {\n" +

					//change it to use lock/unlock
					//tab + tab + tab + "long THREAD_START_TIME = System.currentTimeMillis();\n" +

					//TODO initially these variables are going to be
					//initialised with a random value. It should be a non-deterministic value
					//that meets the predicates in the guard.
					//init_ps +
					init_params_threaded +
					//tab + tab + tab + "if(guard_"+evtName+"("+ps+")) {\n" +
					//tab + tab + tab + tab + "Utilities.lock(eventId); // start of critical section\n" +
					//tab + tab + tab + tab + "run_" + evtName +"("+ps+");\n" +
					//tab + tab + tab + tab + "Utilities.unlock(eventId); // end of critical section\n"+
					//tab + tab + tab + "}\n"+

					tab + tab + tab + "machine.lock.lock(); // start of critical section\n" +
					tab + tab + tab + "run_" + evtName +"("+ps+");\n" +
					tab + tab + tab + "machine.lock.unlock(); // end of critical section\n"+

				//change it to use lock/unlock
				//tab + tab + tab + "long THREAD_END_TIME = System.currentTimeMillis();\n" +
				//tab + tab + tab + "long THREAD_TIME_TAKEN = THREAD_END_TIME - THREAD_START_TIME;\n" +
				//tab + tab + tab + "try{\n" +
				//tab + tab + tab + tab + "Thread.sleep(Math.max(250 - THREAD_TIME_TAKEN,0));\n" +
				//tab + tab + tab + "}\n" +
				//tab + tab + tab + "catch (InterruptedException e){\n" +
				//tab + tab + tab + tab + "e.printStackTrace();\n" +
				//tab + tab + tab + tab + "return;\n" +
				//tab + tab + tab + "}\n" +
				tab + tab + "}\n" +
				tab + "}\n";
		}
		res += "}\n";

		/*** for non-threaded version ***/
		initialisation_params += init_prs; 
		framework_guard_while += guard_while;
		framework_body_while += body_while;
		new_value_params += new_val_prs;
		/*** for non-threaded version ***/
		return res;
	}

	public String ruleNeg(String predG){
		return "!" + predG;
	}

	public String ruleSkip(){
		return "true";
	}

	public String ruleAsg(String var, String assignment){
		String res = "";
		res += var + ".equals(\\old(" + assignment + "))";
		return res;
	}

	public String getInternalType(String varName){
		String res;
		if (with_exception){
			try
			{
				res = Pred2Java.getInternalType(varName);
			}
			catch (Exception ex)
			{
				res = "(* Error *)";
			}
		}else{
			res = Pred2Java.getInternalType(varName);
		}
		return res;
	}

	public String getJmlType(String varName){
		String res;
		if (with_exception){
			try{
				res = Pred2Java.getJmlType(varName);
			}catch (Exception ex){
				res = "(* Error *)";
			}
		}else{
			res = Pred2Java.getJmlType(varName);
		}
		return res;
	}

	public String transPred(String pred, boolean trans_imp){
		String res = "";
		if (with_exception){
			try
			{
				res = Pred2Java.Pre(pred,trans_imp);
			}
			catch (Exception ex)
			{
				res = "(* Error *)";
			}
		}else{
			res = Pred2Java.Pre(pred,trans_imp);
		}
		return res; 
	}

	public void transExp(String exp){
		if (with_exception){
			try
			{
				Pred2Java.Exp(exp);
			}
			catch (Exception ex)
			{
			}
		}else{
			Pred2Java.Exp(exp);
		}
	}

	public String transExp_variant(String exp){
		String res = "";
		if (with_exception){
			try
			{
				res = Pred2Java.variant(exp);
			}
			catch (Exception ex)
			{
				res = "(*ERROR*)";
			}
		}else{
			res = Pred2Java.variant(exp);
		}
		return res;
	}

	public HashMap<String, ArrayList<String>> transAssig(String assig){
		return Pred2Java.Assignment(assig);
	}

	public String getType(String varName, String varDef){
		String res;
		if (with_exception){
			try{
				res = Pred2Java.getvariableType(varName, varDef,true); 
			}catch (Exception ex){
				res = "(* error *)";
			}
		}else{
			res = Pred2Java.getvariableType(varName, varDef,true);
		}
		return res;
	}

	// Returns machine 'machineName' refined machines in EventB to JML
	public ISCRefinesMachine[] machineRefined(IRodinFile rodinFile, String machineName) throws CoreException {
		ISCRefinesMachine[] refinedMachines =  utils.fetchRefinedMachines(rodinFile, machineName);
		return refinedMachines;
	}

	// Returns machine 'machineName' invariants (and theorems) in EventB to JML
	public String machineInvariants(IRodinFile rodinFile, String machineName) throws CoreException {
		StringBuffer res = new StringBuffer("");
		ISCInvariant[] invariants =  utils.fetchInvariants(rodinFile,machineName);
		if (invariants.length > 0){
			res = new StringBuffer(tab + "/*@ public invariant\n");
		}
		String trans;
		for(int i=0; i < invariants.length; i++){
			PrintTrace("Inv: "+ invariants[i].getLabel());
			//translationTrace(invariants[i].getLabel(),"inv1");
			trans = tab + tab +  transPred(invariants[i].getPredicateString(),false);
			if (i != invariants.length-1){
				trans += " &&\n";
			}

			res.append(trans);
		}
		Pred2Java.as = false;
		if (invariants.length > 0)
			res.append("; */\n");

		//Retrieving all theorems
		ISCInvariant[] theorems =  utils.fetchMachineTheorems(rodinFile,machineName);
		if (theorems.length > 0)
			res.append(tab + "/*@ public invariant_redundantly\n");
		trans = "";
		for(int i=0; i < theorems.length; i++){
			PrintTrace("Theorem: "+ theorems[i].getLabel());
			//translationTrace(theorems[i].getLabel(),"thm2_m1");
			trans = tab +  transPred(theorems[i].getPredicateString(),false);
			if (i != theorems.length-1){
				trans += " &&\n";
			}

			res.append(trans);
		}
		if (theorems.length > 0)
			res.append("; */\n");
		return res.toString().replaceAll("machine.", "");
	}


	public String ClassCreation(ArrayList<String> names){
		String res = "";
		for (int i = 0; i <names.size();i++){
			res += tab + names.get(i) + " evt_" + names.get(i) +" = new " + names.get(i) + "(this);\n";
		}
		return res;
	}

	public String ThreadCreation(ArrayList<String> names){
		String res = tab + tab + "events = new Thread[n_events];\n";
		for (int i = 0; i <names.size();i++){
			res += tab + tab + "events[" + i + "] = new "+ names.get(i) +"(this);\n";
		}
		res += "\n";
		res += tab + tab + "for (int i = 0; i < n_events;i++){\n" +
				tab + tab + tab + "events[i].start();\n" +
				tab + tab + "}";
		return res;
	}

	//Returns variable's type
	public String varType(ISCVariable var) throws CoreException {
		final FormulaFactory f = FormulaFactory.getDefault();

		//translationTrace(var.getElementName(),"a");
		String varType = getType(var.getElementName(), var.getType(f).toString());
		return varType;
	}



	//Returns variable (var) in B into JML.
	public String variable(ISCVariable var) throws CoreException {
		//translationTrace(var.getIdentifierString(), "t");
		String type = varType(var);
		String v = tab + "/*@ spec_public */ private " + type + " " + var.getIdentifierString() + ";\n\n";
		var_methods.put(var.getIdentifierString(), type);
		Pred2Java.as = false;
		return v;
	}

	// Returns machine 'machineName' variables in EventB to JML
	public String machineVariables(IRodinFile rodinFile, String machineName) throws CoreException {
		/*
		 * Gets all the variables of the machine. It stores them and
		 * the type of each variable is calculated when the invariants
		 * are being translated.
		 */
		StringBuffer res = new StringBuffer("");
		ISCVariable[] variables = utils.fetchMachineVariables(rodinFile,machineName);
		for (ISCVariable var : variables){
			res.append(variable(var));
			all_variables.add(var.getIdentifierString());
			variablesModel.add(var.getIdentifierString());
		}
		return res.toString();
	}

	// Returns event 'event' refine clause of machine 'machineName' in EventB to JML
	public String eventRefines(ISCEvent event) throws CoreException {
		System.out.println("================ Refines");
		StringBuffer res = new StringBuffer("");
		ISCRefinesEvent[] evtRefs = utils.fetchEvtRefines(event);
		for (ISCRefinesEvent evtRef : evtRefs)
			res.append(evtRef.getElementName());
		return res.toString();
	}

	public String ParameterType(ISCParameter param) throws CoreException {
		final FormulaFactory f = FormulaFactory.getDefault();
		PrintTrace("parameter: " + param.getElementName());
		/*if (param.getElementName().equals("rawmaterialpro")){
			Pred2Java.as = true;
		}else
			Pred2Java.as = false;*/
		String parameterType = getType(param.getElementName(), param.getType(f).toString());

		return parameterType;
	}

	// Returns event 'event' parameters of machine 'machineName' in EventB to JML
	public LinkedHashMap<String,String> eventParameters(ISCEvent event) throws CoreException {
		LinkedHashMap<String,String> parameter = new LinkedHashMap<String,String>();
		ISCParameter[] evtParameters = utils.fetchEvtParameters(event);
		for( ISCParameter par: evtParameters){
			String p = par.getElementName();
			String Type = ParameterType(par);
			parameter.put(p, Type);
		}
		return parameter;
	}

	// Returns event 'event' guards of machine 'machineName' in EventB to JML
	public ArrayList<String> eventGuards(ISCEvent event) throws CoreException {
		ArrayList<String> res = new ArrayList<String>(); 
		StringBuffer res_jml = new StringBuffer("");
		StringBuffer res_java = new StringBuffer("");
		ISCGuard[] evtGuards = utils.fetchEvtGuards(event);
		for (int i=0; i<evtGuards.length;i++){
			PrintTrace("guard: " + evtGuards[i].getLabel());
			/*if (event.getLabel().equals("delete_content"))
				translationTrace(evtGuards[i].getLabel(), "grd6");
			else
				Pred2Java.as = false;*/

			res_jml.append(transPred(evtGuards[i].getPredicateString(),false));
			String java = transPred(evtGuards[i].getPredicateString(),true);
			if (!(java.contains("\\forall") || java.contains("\\exists"))){
				res_java.append(java);
			}else{
				res_java.append("true");
			}


			if (i < evtGuards.length-1){
				res_jml.append(" && ");
				res_java.append(" && ");
			}
		}

		if (evtGuards.length > 1){
			res.add("(" + res_jml.toString() + ")");
			res.add("(" + res_java.toString() + ")");
			return res;
		}else{
			res.add(res_jml.toString());
			res.add(res_java.toString());
			return res;
		}
	}

	// Returns event 'event' actions of machine 'machineName' in EventB to JML
	public ArrayList<String> eventActions(ISCEvent event) throws CoreException {
		String tmp_vars = "";
		String assg_java = "";
		String act_jml = "";
		ArrayList<String> res = new ArrayList<String>();
		vars_mod = new ArrayList<String>();
		ISCAction[] evtActions =  utils.fetchEvtActions(event);
		int i = evtActions.length;

		for (ISCAction evtAction : evtActions){
			String var = evtAction.getAssignmentString().split(" ")[0];
			vars_mod.add(var);
			//tmp_vars += tab + tab + tab + getJmlType(var) + " " +var + "_tmp = machine.get_" + var + "();\n";
			tmp_vars += tab + tab + tab + getJmlType(var) + " " +var + "_tmp = machine.get_" + var + "();\n";
		}

		for (ISCAction evtAction : evtActions){
			PrintTrace(evtAction.getLabel());
			//todolete
			/*if (event.getLabel().equals("broadcast")){
				JmlType.as = true;
				translationTrace(evtAction.getLabel(), "actr13");
			}else{
				Pred2Java.as = false;
				JmlType.as = false;
			}*/
			
			HashMap<String,ArrayList<String>> assi = transAssig(evtAction.getAssignmentString());
			for (String var : assi.keySet()){
				String tt = getInternalType(var);
				if (assi.get(var).get(0).equals("BECOMES")){//TODO magic words: get rid of them!
					act_jml += assi.get(var).get(1);

					String t_becomes = Pred2Java.transBecomes;

					String initValue = "";
					if (t_becomes.contains(".instance")){
						if (t_becomes.contains("BOOL.instance")){
							initValue = t_becomes.replace("BOOL.instance","BOOL.instance");
						}else if (t_becomes.contains("INT.instance")){
							initValue = t_becomes.replace("INT.instance","new Enumerated(machine.min_integer, machine.max_integer)");
						}else if (t_becomes.contains("NAT.instance")){
							initValue = t_becomes.replace("NAT.instance", "new Enumerated(0, machine.max_integer)");
						}else{ // it is a NAT1.instance
							initValue = t_becomes.replace("NAT1.instance", "new Enumerated(1, machine.max_integer)");
						}
					}else{
						if (t_becomes.equals("Integer")){
							initValue = "new Enumerated(machine.min_integer, machine.max_integer)";
						}else{
							initValue = t_becomes;
						}
					}
					assg_java += tab + tab + "machine.set_" + var + "(Utilities.someVal("+ initValue +"));\n";

				}else{ 
					if (assi.get(var).get(0).equals("NONDET")){

						act_jml += assi.get(var).get(1);
						non_det_guard += assi.get(var).get(1) + " && "; 
						String predicate = assi.get(var).get(3).replaceAll("tmp_", "machine.");
						for (String non_det_var: assi.get(var).get(2).split(",")){
							assg_java += tab + tab + "//machine." +non_det_var + " = Utilities.non_det_assignment(" + 
									non_det_var + "_tmp,(" + 
									concurrencySupport(predicate) + "));\n";
						}
					}else{
						if (tt.equals(JmlType.intT) || tt.equals(JmlType.boolT)){
							act_jml += " machine." + var + " == \\old(" + assi.get(var).get(1) + ")";
							assg_java += tab + tab + tab + "machine.set_"+var + "(" + concurrencySupport(assi.get(var).get(1)) + ");\n";
						}else if (tt.equals(JmlType.setT) || tt.equals(JmlType.relT) || tt.equals(JmlType.pairT)){
							act_jml += " machine." + var + ".equals(\\old(" + assi.get(var).get(1) + "))";
							if (assi.get(var).get(0).equals("QuantifiedExpression")){
								//(07.11)VR: Bug SetComprehension
								//		Type was not being translated correctly
								// 		add (null) and the comment.
								assg_java += tab + tab + tab + "machine.set_"+var + "(null); // Set Comprehension: feature not supported by EventB2Java\n";
							}else {
								assg_java += tab + tab + tab + "machine.set_"+var + "(" + concurrencySupport(assi.get(var).get(1)) + ");\n";
							}
						}else{
							act_jml += tab + tab + tab + "FIXIT - EventB2Java - eventActions";
						}
					}
				}
				if (i > 1){
					act_jml += " && ";
				} i--;
			}
		}

		res.add(act_jml);
		res.add(tmp_vars + "\n" + assg_java);
		return res;
	}

	public String concurrencySupport(String v){
		//vars contains the vars to be assigned in a specific event 
		String res = v;
		for (String vr : all_variables){
			if (vars_mod.contains(vr)){
				//res = res.re .regionMatches(arg0, arg1, arg2, arg3) replaceAll("machine."+vr, vr+"_tmp");
				res = res.replaceAll("machine."+"\\b"+vr+"\\b", vr+"_tmp");
			}else if (variablesModel.contains(vr)){
				res = res.replaceAll("machine."+"\\b"+vr+"\\b", "machine.get_"+vr+"()");
			}
		}
		return res;
	}

	@Override
	public void selectionChanged(IAction action, ISelection selection) {
		this.selection = selection;
	}

	public String eventWitnesses(ISCEvent event) throws CoreException {
		System.out.println("================ Witnesses");
		return "";
	}
	// Returns machine 'machineName' variants in EventB to JML
	public String machineVariants(IRodinFile rodinFile, String machineName) throws CoreException {
		System.out.println("================ machineVariants");
		String variant = "";

		ISCVariant[] variants =  utils.fetchVariants(rodinFile,machineName);
		
		for (ISCVariant v: variants){
			variant = transExp_variant(v.getExpressionString());
		}

		return variant;
	}

	public void print(String s){
		System.out.println(s);
	}
	public void print(int s){
		System.out.println(s);
	}

	public void translationTrace(String label, String s){
		if (label.equals(s))
			Pred2Java.as = true;
		else Pred2Java.as = false;
	}

	public boolean pt = false;
	public void PrintTrace(String s){
		if (pt)
			System.out.println(s);
	}

	private ISelection selection;

	private IRodinFile getSelectedComponent() {
		if (selection instanceof IStructuredSelection) {
			final IStructuredSelection ssel = (IStructuredSelection) selection;
			if (ssel.size() == 1) {
				return EventBPlugin.asEventBFile(ssel.getFirstElement());
			}
		}
		return null;
	}

	private String utilityFile(){
		return "" +
				"package Util;\n" +
				"import java.util.Random;\n" +
				"import eventb_prelude.*;\n" +
				"\n" +
				"public class Utilities {\n" +
				tab + "//Class Utilities implements the Bakery Algorithm and\n" + 
				tab + "// the support for non-determinism assignment\n" +
				"\n" +
				tab + "public volatile static int[] turn; // ticket number for event i; if turn[i] == 0 then event i has no turn allocated yet\n" +
				tab + "public volatile static boolean[] want;\n" +
				"\n" +
				tab + "public Utilities(int size){\n" +
				tab + tab + "want = new boolean[size];\n" +
				tab + tab + "turn = new int[size];\n" +
				tab + tab + "for (int i = 0; i < size; i++){\n" +	
				tab + tab + tab + "turn[i] = 0;\n" +
				tab + tab + "}\n" +
				tab + tab + "for (int i = 0; i < size; i++){\n" +	
				tab + tab + tab + "want[i] = false;\n" +
				tab + tab + "}\n" +
				tab + "}\n" +
				"\n" +
				tab + "public static Integer max(int[] array){\n" +
				tab + tab + "Integer m;\n" +
				tab + tab + "if (array.length <= 0)\n" +
				tab + tab + tab + "return null;\n" +
				tab + tab + "else\n" +
				tab + tab + tab + "m = array[0];\n" +
				"\n" +
				tab + tab + "for(int i=0;i<array.length;i++){\n" +
				tab + tab + tab + "if (array[i] > m)\n" +
				tab + tab + tab + tab + "m = array[i];\n" +
				tab + tab + "}\n" +
				tab + tab + "return m;\n" +
				tab + "}\n" +
				"\n" +
				tab + "public static void lock(int eid){\n" +
				tab + tab + "want[eid] = true;\n" +
				tab + tab + "turn[eid] = max(turn) + 1;\n" +
				tab + tab + "want[eid] = false;\n" +
				tab + tab + "for (int j=0; j < turn.length; j++) {\n" +
				tab + tab + tab + "while (want[j]) {}\n" +
				tab + tab + tab + "while ((turn[j] != 0) &&\n" +
				tab + tab + tab + tab + "((turn[j] < turn[eid]) ||\n" +
				tab + tab + tab + tab + "((turn[j] == turn[eid]) && ((j < eid))))){}\n" +
				tab + tab + "}\n" +
				tab + "}\n" +
				"\n" +
				tab + "public static void unlock(int eid){\n" +
				tab + tab + "turn[eid] = 0;\n" +
				tab + "}\n" +
				"\n\n" +
				tab + "public static Integer min_integer = -100;\n"+
				tab + "public static Integer max_integer = 100;\n"+
				tab + "public static <T> T someVal(BSet<T> s){\n" +
				tab + tab + "if (s.isEmpty()){\n" +
				tab + tab + tab + "return null;\n" +
				tab + tab + "}else if (s.size() == 1){\n" +
				tab + tab + tab + "return s.choose();\n" +
				tab + tab + "}\n" +
				tab + tab + "Random rnd = new Random();\n" +
				tab + tab + "int value = rnd.nextInt(s.size()-1);\n" +
				tab + tab + "if (s instanceof BRelation){\n" +
				tab + tab + tab + "return (T) (((BRelation) s).toSet().toArray()[value]); \n" +
				tab + tab + "}else{\n" +
				tab + tab + tab + "return (T) (s.toArray()[value]); \n" +
				tab + tab + "}\n" +
				tab + "}\n" +
				tab + "public static <T> BSet<T> someSet(BSet<T> s){\n"+
				tab + tab + "if (s.isEmpty()){\n" + 
				tab + tab + tab + "return null;\n"+
				tab + tab + "}else if (s.size() == 1){\n" +
				tab + tab + tab + "return s;\n" +
				tab + tab + "}\n" +
				tab + tab + "BSet<T> res = new BSet<T>();\n" +
				tab + tab + "Random rnd = new Random();\n" +
				tab + tab + "int iterations = rnd.nextInt(Utilities.max_integer);\n" + 
				tab + tab + "for (int i=0;i<iterations;i++){\n" +
				tab + tab + tab + "int value = rnd.nextInt(s.size()-1);\n" +
				tab + tab + tab + "if (s instanceof BRelation){\n" +
				tab + tab + tab + tab + "res.add((T) (((BRelation) s).toSet().toArray()[value]));\n" +
				tab + tab + tab + "}else{\n" +
				tab + tab + tab + tab + "res.add((T) (s.toArray()[value]));\n" +
				tab + tab + tab + "}\n" +
				tab + tab + "}\n" +
				tab + tab + "return res;\n" +
				tab + "}\n\n" +
				tab + "public static <T> T non_det_assignment(T var, boolean predicate){\n" +
				tab + tab + "//No supported yet\n" +
				tab + tab + "return null;\n" +
				tab + "}\n" + 
				"}\n";
	}
	

	@SuppressWarnings("unchecked")
	private String testFile(String name_test, String name_mainClass, String pack, ArrayList<String> name_evts) throws Exception{
		String res = "";
		String consts_def = "";
		String consts_init = "";
		
		// Initializing the constraint solver
		Injector INJECTOR = Guice.createInjector(Stage.PRODUCTION, new GuiceConfig());
		ConstraintSolver constraintSolver = INJECTOR.getInstance(ProB.class);
		try {
			final IRodinFile rodinFile = getSelectedComponent();
			constraintSolver.load(rodinFile.getCorrespondingResource().getLocation().toString());
			constraintSolver.generateValuesForConstants();
		} catch (Exception e) {
			e.printStackTrace();
		}
		
		// Output for constants with generated values 
		String value;
		for (String c : constantsVars.keySet()){
			value = "null";
			consts_def += tab + "public static " + constantsVars.get(c).get(0) + " random_" + c + ";\n";
			String internal_type = constantsVars.get(c).get(1);
			
			// Boolean value
			if (internal_type.equals(JmlType.boolT)) {
				if (constraintSolver.getGeneratedBooleanValue(c) != null) {
					value = constraintSolver.getGeneratedBooleanValue(c).toString();
				}
				consts_init += tab + tab + "test.random_" + c + " = " + value + ";\n";
			} 
			// Integer value
			else if (internal_type.equals(JmlType.intT)) {
				if (constraintSolver.getGeneratedIntegerValue(c) != null) {
					value = constraintSolver.getGeneratedIntegerValue(c).toString();
				}
				consts_init += tab + tab + "test.random_" + c + " = " + value + ";\n";
			}
			// BSet value 
			else if (internal_type.equals(JmlType.setT)) {	
				consts_init += tab + tab + "test.random_ = " + c
						+ "new BSet<Integer>();\n";
				if (!constraintSolver.getGeneratedBSet(c).isEmpty()) {
					for (Object o : constraintSolver.getGeneratedBSet(c)) {
						consts_init += tab + tab + "test.random_" + c +
								 ".add(" + o.toString() + ");\n";
						 
					}
				}
			} 
			// BRelation value
			else if (internal_type.equals(JmlType.relT)) {
				consts_init += tab + tab +"test.random_" + c
						+ "= new BRelation<Integer,Integer>();\n";
				if (!constraintSolver.getGeneratedBRelation(c).isEmpty()) {
					Map<Object, Object> generatedSet = constraintSolver.getGeneratedBRelation(c);
					java.util.Set unsortedKeySet = generatedSet.keySet(); 
					List keySet = new ArrayList(unsortedKeySet);
					Collections.sort(keySet, new Comparator() 
					{
						@Override
						public int compare(Object o1, Object o2) {
							if (Integer.parseInt(o1.toString()) >= Integer.parseInt(o2.toString())) {
								return 1;
							}
							return -1;
						}
					}
					);
					
					for (Object key : keySet) {
						consts_init += tab + tab + "test.random_" + c +
								".add(new Pair<Integer, Integer>(" + 
								key.toString() + ", " + 
								generatedSet.get(key).toString() + 
								"));\n";
					}
				}
			} 
			// Another case
			else {
				consts_init += tab + tab + "test.random_" + c + " = null; //No suggestion\n";
			}
		}
		
		
		/**for (String c : constantsVars.keySet()){
			consts_def += tab + "public static " + constantsVars.get(c).get(0) + " random_" 
					+ c + ";\n";
			String internal_type = constantsVars.get(c).get(1);
			if (internal_type.equals(JmlType.boolT)){
				consts_init += tab + tab + "test.random_" + c + " = test.GenerateRandomBoolean();\n";
			}else if (internal_type.equals(JmlType.intT)){
				consts_init += tab + tab + "test.random_" + c + " = test.GenerateRandomInteger();\n";
			}else if (internal_type.equals(JmlType.setT)){
				//BSet<Integer>
				consts_init += tab + tab + "test.random_" + c + " = test.GenerateRandomIntegerBSet();\n";
			}else if (internal_type.equals(JmlType.relT)){
				consts_init += tab + tab + "test.random_" + c + " = test.GenerateRandomBRelation();\n";
			}else{
				consts_init += tab + tab + "test.random_" + c + " = null; //No suggestion\n";
			}
		}*/


		res =  "" +
				"package "+pack+";\n" +
				"import java.util.Random;\n" +
				"import Util.Utilities;\n" +
				"import eventb_prelude.*;\n" +
				"\n" +
				//TODO
				//"/*BEGIN CUSTOMISATION: Importing Classes */\n" +
				//"/*END CUSTOMISATION: Importing Classes */\n\n" +
				"public class " + name_test + "{\n\n" +
				consts_def + "\n" +
				tab + "static Random rnd = new Random();\n" +
				tab + "static Integer max_size_BSet = 10;\n" +
				tab + "Integer min_integer = Utilities.min_integer;\n" +
				tab + "Integer max_integer = Utilities.max_integer;\n" +
				"\n" +
				tab + "public Integer GenerateRandomInteger(){\n" +
				tab + tab + "BSet<Integer> S =  new BSet<Integer>(\n" +
				tab + tab + tab + tab + "new Enumerated(min_integer, max_integer)\n" +
				tab + tab + tab + tab + ");\n" +
				tab + tab + "/** User defined code that reflects axioms and theorems: Begin **/\n\n" +
				tab + tab + "/** User defined code that reflects axioms and theorems: End **/\n\n" +
				tab + tab + "return (Integer) S.toArray()[rnd.nextInt(S.size())];\n" +
				tab + "}\n" +
				"\n" +
				tab + "public boolean GenerateRandomBoolean(){\n" +
				tab + tab + "boolean res = (Boolean) BOOL.instance.toArray()[rnd.nextInt(2)];\n\n"+
				tab + tab + "/** User defined code that reflects axioms and theorems: Begin **/\n\n" +
				tab + tab + "/** User defined code that reflects axioms and theorems: End **/\n\n" +
				tab + tab + "return res;\n" +
				tab + "}\n" +
				"\n" +
				"\n" +
				tab + "public BSet<Integer> GenerateRandomIntegerBSet(){\n" +
				tab + tab + "int size = rnd.nextInt(max_size_BSet);\n" +
				tab + tab + "BSet<Integer> S = new BSet<Integer>();\n" +
				tab + tab + "while (S.size() != size){\n" +
				tab + tab + tab + "S.add(GenerateRandomInteger());\n" +
				tab + tab + "}\n\n" +
				tab + tab + "/** User defined code that reflects axioms and theorems: Begin **/\n\n" +
				tab + tab + "/** User defined code that reflects axioms and theorems: End **/\n\n" +
				tab + tab + "return S;\n" +
				tab + "}\n" +
				"\n" +
				tab + "public BSet<Boolean> GenerateRandomBooleanBSet(){\n" +
				tab + tab + "int size = rnd.nextInt(2);\n" +
				tab + tab + "BSet<Boolean> res = new BSet<Boolean>();\n"+
				tab + tab + "if (size == 0){\n" +
				tab + tab + tab + "res = new BSet<Boolean>(GenerateRandomBoolean());\n" +
				tab + tab + "}else{\n" +
				tab + tab + tab + "res = new BSet<Boolean>(true,false);\n" +
				tab + tab + "}\n\n" +
				tab + tab + "/** User defined code that reflects axioms and theorems: Begin **/\n\n" +
				tab + tab + "/** User defined code that reflects axioms and theorems: End **/\n\n" +
				tab + tab + "return res;\n" +
				tab + "}\n" +
				"\n" +
				tab + "public BRelation<Integer,Integer> GenerateRandomBRelation(){\n" +
				tab + tab + "BRelation<Integer,Integer> res = new BRelation<Integer,Integer>();\n" +
				tab + tab + "int size = rnd.nextInt(max_size_BSet);\n" +
				tab + tab + "while (res.size() != size){\n" +
				tab + tab + tab + "res.add(\n" +
				tab + tab + tab + tab + tab + "new Pair<Integer, Integer>(GenerateRandomInteger(), GenerateRandomInteger()));\n" +
				tab + tab + "}\n" +
				tab + tab + "/** User defined code that reflects axioms and theorems: Begin **/\n\n" +
				tab + tab + "/** User defined code that reflects axioms and theorems: End **/\n\n" +
				tab + tab + "return res;\n" +
				tab + "}\n\n" +
				//TODO
				//tab + "/*BEGIN CUSTOMISATION */\n" +
				//tab + "/*END CUSTOMISATION */\n\n" +
				tab + "public static void main(String[] args){\n" +
				tab + tab + ""+name_test+" test = new "+name_test+"();\n\n" +
				tab + tab + "/** User defined code that reflects axioms and theorems: Begin **/\n" +
				consts_init +
				tab + tab + "/** User defined code that reflects axioms and theorems: End **/\n\n";
		if (threaded){
			res += tab + tab + "new "+ name_mainClass +"();\n";

		}else{
			res += tab + tab + name_mainClass + " machine = new "+ name_mainClass +"();\n";
			res += Environment(name_evts.size());
		}
		res += tab + "}\n" +
				"\n" +
				"}\n";

		return res;

	}

	public static String BodyMethod(String type){
		String res = "";
		String tab = "\t";
		String[] splt = type.split("<");
		for (int i=0;i<splt.length-2;i++){
			res += tab + type + " tmp_" + (i+1) + " =  new " + type + "();\n" ;
			if (i+1 == splt.length-2 && splt[splt.length-1].contains("Boolean")){
				res += tab + "int size_" + (i+1) +" = rnd.nextInt(2);\n" ;
			}else{
				res += tab + "int size_" + (i+1) +" = rnd.nextInt(max_size_BSet);\n" ;
			}
			res += tab + "while (tmp_" + (i+1) + ".size() != size_" + (i+1) +"){\n" ;
			tab += "\t";
			String g = type.replaceFirst("BSet<", "");
			type = g.substring(0, g.length()-1);
		}
		int times = splt.length-2;
		if (splt[splt.length-1].contains("Integer")){
			res += tab + "tmp_" + times +".add(GenerateRandomIntegerBSet());\n" ;
		}else{
			res += tab + "tmp_" + times +".add(GenerateRandomBooleanBSet());\n" ;
		}
		for (;times>0;times--){
			tab = tab.replaceFirst("\t", "");
			res += tab + "}\n" ;
			if (times > 1){
				res += tab + "tmp_" + (times-1) + ".add(tmp_" + times +");\n" ;
			}
		}
		res += tab + "return tmp_1;\n" ;
		return res;
	}

	public static String GenerateGenericBSetMethod(String type, String var){
		String newMethod = "public static " + type + " GenerateRandom_" + var + "(){\n" ;
		newMethod += BodyMethod(type);
		newMethod += "}";
		return newMethod; 
	}

	private static void displayInStatusBar(String message, boolean error) {
		final IWorkbenchWindow activeWorkbenchWindow = PlatformUI
				.getWorkbench().getActiveWorkbenchWindow();
		if (activeWorkbenchWindow == null)
			return;
		final IWorkbenchPage page = activeWorkbenchWindow.getActivePage();
		if (page == null)
			return;
		final IViewPart view = page
				.findView("fr.systerel.explorer.navigator.view");
		if (view == null)
			return;
		final IViewSite site = view.getViewSite();
		final IStatusLineManager slManager = site.getActionBars()
				.getStatusLineManager();
		slManager.setMessage(message);
	}

	private String any_parameter_initialisation(String name, JmlType type){

		String init_par = name + " = " +
				"Utilities.someVal(new BSet<?inter_type?>(";
		if (type.getInternalType().equals(JmlType.intT)){ //TODO: I need to recognize if it is N0, N1, or Z
			init_par = init_par.replace("?inter_type?", JmlType.intT);
			init_par += "(new Enumerated(1,Utilities.max_integer))));\n";
		}else if (type.getInternalType().equals(JmlType.boolT)){
			init_par = init_par.replace("?inter_type?", JmlType.boolT);
			init_par += "(true,false)));\n";
		}else if (type.getInternalType().equals(JmlType.setT)){
			init_par = init_par.replace("someVal", "someSet");
			init_par = init_par.replace("?inter_type?", type.getSetType().getJmlType());
			if (type.getSetType().getInternalType().equals(JmlType.boolT)){
				init_par += "new BSet<" + JmlType.boolT + ">(true,false)));\n";
			}else{
				init_par += "(new Enumerated(1,Utilities.max_integer))));\n";
			}
		}else if (type.getInternalType().equals(JmlType.relT)){
			//TODO to implement
			init_par = name + " = null; //not supported yet\n";
		}else if (type.getInternalType().equals(JmlType.pairT)){
			//TODO to implement
			init_par = name + " = null; //not supported yet\n";
		}else{
			init_par = name + " = null; //not supported yet\n"; 
		}
		return init_par;
	}


	private String Environment(int n_events){
		String res = "";
		if (n_events == 0){
			res = "\n";
		}else{
			res = tab + tab + "int n = " + n_events + "; //the number of events in the machine\n"+ 
					initialisation_params +
					//tab + tab + "while (\n"+ framework_guard_while +
					tab + tab + "while (true){\n" +
					tab + tab + tab + "switch (rnd.nextInt(n)){\n"+
					framework_body_while + 
					tab + tab + tab + "}\n" +
					new_value_params + 
					tab + tab + "}\n";
		}
		return res;
	}


	public String create_getter_setter_methods(){
		String res = "";
		for (String name_evt: var_methods.keySet()){
			//getter method
			res += tab + "/*@ public normal_behavior\n"; 
			res += tab + "    requires true;\n";
			res += tab + "    assignable \\nothing;\n";
			res += tab + "    ensures \\result == this."+name_evt+";*/\n";
			res += tab + "public /*@ pure */ " + var_methods.get(name_evt) + " get_" + name_evt + "(){\n";
			res += tab + tab + "return this." + name_evt + ";\n";
			res += tab + "}\n\n";
			//mutator method
			res += tab + "/*@ public normal_behavior\n";
			res += tab + "    requires true;\n";
			res += tab + "    assignable this."+ name_evt +";\n";
			res += tab + "    ensures this."+name_evt+" == "+name_evt+";*/\n";
			res += tab + "public void set_" + name_evt + "("+ var_methods.get(name_evt) + " " + name_evt + "){\n";
			res += tab + tab + "this." + name_evt + " = "+ name_evt +";\n";
			res += tab + "}\n\n";
		}
		return res;
	}

	//Checks if path+nameFile exists. It returns the information within the customisation tags.
	//There are three kind of tags: importing - code - axioms/theorems. This method will return the tags
	//according to the kind of file: main/event/test
	//it could be improved by implementing a parser
	//type -> 1. main file
	//		  2. event file
	//		  3. test file
	private HashMap<String,String> customised_code(String path, String name, int type) throws IOException{
		HashMap<String,String> customised_tags = new HashMap<String,String>();
		File f = new File(path + File.separator + name);

		if (f.exists()){
			BufferedReader reader = new BufferedReader(new FileReader(path + File.separator + name));
			String line = null;
			while ((line = reader.readLine()) != null) {
				//importing
				if (line.contains("/*BEGIN CUSTOMISATION: Importing Classes */"))
					System.out.println("=>> " + line);
			}
			if (type == 1){
				//to parse the file

				//1. searching for information about customised classes import
			}else if (type == 2){

			}else{ //type == 3

			}
		}

		return customised_tags;
	}

	private void create_prelude(String path) throws IOException{
		String BOOL =
				"package eventb_prelude;\n" + 
						"\n" + 
						"/** a class to represent type BOOL as a set in JML \n" + 
						" * @author Tim Wahls & Nestor Catano & Victor Rivera\n" + 
						" */\n" + 
						"\n" + 
						"public class BOOL extends BSet<Boolean> {\n" + 
						"	public static final BOOL instance = new BOOL();\n" + 
						"	\n" + 
						"	/*@ public static initially BOOL.instance.has(true) && BOOL.instance.has(false); */\n" + 
						"	\n" + 
						"	private BOOL() {\n" + 
						"		add(true);\n" + 
						"		add(false);\n" + 
						"	}\n" + 
						"	\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result == (p ==> q);\n" + 
						"	*/\n" + 
						"	public /*@ pure */ static boolean implication(boolean p, boolean q){\n" + 
						"		return (!p || q);\n" + 
						"	}\n" + 
						"	\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result == (p <==> q);\n" + 
						"	*/\n" + 
						"	public /*@ pure */ static boolean bi_implication(boolean p, boolean q){\n" + 
						"		return (p && q) || (!p && !q);\n" + 
						"	}\n" + 
						"}";

		String BRelation =
				"package eventb_prelude;\n" + 
						"\n" + 
						"import java.util.TreeSet;\n" + 
						"import java.util.Iterator;\n" + 
						"\n" + 
						"/** a class to model Event-B relations in Java \n" + 
						" * @author Tim Wahls & Nestor Catano & Victor Rivera\n" + 
						" */\n" + 
						"\n" + 
						"public class BRelation<K, V> extends BSet<Pair<K, V>> {\n" + 
						"	public static BRelation EMPTY = new BRelation();\n" + 
						"	\n" + 
						"		/*@ requires true;\n" + 
						"		 	ensures this.isEmpty();\n" + 
						"		 */\n" + 
						"		public BRelation() { }\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	ensures this.equals(elems);\n" + 
						"		 */\n" + 
						"		BRelation(BRelation<K,V> elems) {\n" + 
						"			this();\n" + 
						"			for (Pair<K,V> e : elems)\n" + 
						"				add(e);\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable this.*;\n" + 
						"		  	ensures (\\forall K k; (\\forall V v; this.has(k, v) <==> \n" + 
						"		       			(\\exists int i; 0 <= i && i < pairs.length;\n" + 
						"		          			pairs[i].fst().equals(k) && pairs[i].snd().equals(v))));\n" + 
						"		 */\n" + 
						"		public BRelation(Pair<K,V> ... pairs) {\n" + 
						"			this();\n" + 
						"			for (Pair<K,V> pair : pairs) {\n" + 
						"				add(pair);\n" + 
						"			}\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"	 		assignable this.*;\n" + 
						"	  		ensures (\\forall Pair<K,V> p; this.has(p) <==> s.contains(p));\n" + 
						"		 */\n" + 
						"		public BRelation(BSet<Pair<K,V>> s) {\n" + 
						"			this();\n" + 
						"			addAll(s);\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures \\result.int_size() == 1 && \\result.has(key, value);\n" + 
						"		 */\n" + 
						"		public /*@ pure */ static <KK, VV> BRelation<KK, VV> singleton(KK key, VV value) {\n" + 
						"			return new BRelation<KK, VV>(BRelation.singleton(key, value));\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result.int_size() == 1 && \\result.has(pair);\n" + 
						"	     */\n" + 
						"		public /*@ pure */ static <KK, VV> BRelation<KK, VV> singleton(Pair<KK, VV> pair) {\n" + 
						"			return BRelation.singleton(pair.fst(), pair.snd());\n" + 
						"		}\n" + 
						"\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures (\\forall V v; \\result.has(v) <==> this.has(key, v));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ BSet<V> elementImage(K key) {\n" + 
						"			BSet<V> res = new BSet<V>();\n" + 
						"			for(Pair<K,V> p : this) {\n" + 
						"				if(p.fst().equals(key))\n" + 
						"					res.add(p.snd());\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures (\\forall K key; keys.has(key); \n" + 
						"	          (\\forall V v; \\result.has(v) <==> this.has(key, v)));\n" + 
						"	     */\n" + 
						"		public /*@ pure */ BSet<V> image(BSet<K> keys) {\n" + 
						"			BSet<V> res = new BSet<V>(); // the empty set\n" + 
						"			\n" + 
						"			for(K k : keys) {\n" + 
						"				res.unionInPlace(elementImage(k));\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/* 	requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		   	ensures (\\forall K key; (\\forall V value; \n" + 
						"		     	this.has(key, value) <==> \\result.has(value, key)));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ BRelation<V, K> inverse() {\n" + 
						"			BRelation<V, K> res = new BRelation<V, K>();\n" + 
						"			\n" + 
						"			for(Pair<K,V> pair : this) {\n" + 
						"				res.add(new Pair<V,K>(pair.snd(), pair.fst()));\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"		\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures \\result <==> this.isaFunction();\n" + 
						"		 */\n" + 
						"		public /*@ pure */ boolean isaFunction() {\n" + 
						"			for(Pair<K,V> pair : this) {\n" + 
						"				if(!elementImage(pair.fst()).isSingleton())\n" + 
						"					return false;\n" + 
						"			}\n" + 
						"			return true;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		   ensures (\\forall K key; \\result.has(key) <==> this.has(key, value));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ BSet<K> inverseElementImage(V value) {\n" + 
						"			BSet<K> res = new BSet<K>();\n" + 
						"			for(Pair<K,V> pair : this) {\n" + 
						"				if (pair.snd().equals(value))\n" + 
						"					res.add(pair.fst());\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		   	ensures (\\forall V value; values.has(value);\n" + 
						"		     	(\\forall K key; \\result.has(key) <==> this.has(key, value)));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ BSet<K> inverseImage(BSet<V> values) {\n" + 
						"			BSet<K> res = new BSet<K>();\n" + 
						"			for(V value : values)\n" + 
						"				res.unionInPlace(inverseElementImage(value));\n" + 
						"			\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures \\result <==> (\\exists V value; this.has(key, value));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ boolean isDefinedAt(K key) {\n" + 
						"			for(Pair<K,V> pair : this) {\n" + 
						"				if (pair.fst().equals(key)) return true;\n" + 
						"			}\n" + 
						"			return false;\n" + 
						"		}\n" + 
						"\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable this.*;\n" + 
						"		 	ensures this.has(pair);\n" + 
						"		 */\n" + 
						"		public boolean add(Pair<K,V> pair) {\n" + 
						"			return super.add(pair);\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable this.*;\n" + 
						"		 	ensures this.has(new Pair<K,V>(key,value)); \n" + 
						"		 */\n" + 
						"		public boolean add(K key, V value) {\n" + 
						"			Pair<K,V> pair = new Pair<K,V>(key,value);\n" + 
						"			return add(pair);\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ also\n" + 
						"		    requires true;  \n" + 
						"		    assignable \\nothing;\n" + 
						"		    ensures \\result.equals(insert(pair.fst(), pair.snd()));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ BRelation<K, V> insert(Pair<K, V> pair) {\n" + 
						"			BSet<Pair<K,V>> s = super.insert(pair);\n" + 
						"			return new BRelation<K,V>(s);\n" + 
						"		}\n" + 
						"				\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable this.*;\n" + 
						"		 	ensures \\result.has(new Pair<K,V>(key,value)); \n" + 
						"		 */\n" + 
						"		public BRelation<K, V> insert(K key, V value) {\n" + 
						"			return insert(new Pair<K,V>(key,value));\n" + 
						"		}		\n" + 
						"		\n" + 
						"		/*@ 	also \n" + 
						"		 	requires true;\n" + 
						"		  	assignable \\nothing;\n" + 
						"		    ensures \\result == this.int_size();\n" + 
						"		 */\n" + 
						"		public /*@ pure */ int int_size() {\n" + 
						"			return size();\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures \\result <==> this.has(key, value);\n" + 
						"		 */\n" + 
						"		public /*@ pure */ boolean has(K key, V value) {\n" + 
						"			return super.has(new Pair<K,V>(key, value));\n" + 
						"		}\n" + 
						"		\n" + 
						"		public Object clone() {\n" + 
						"			BRelation<K,V> res = new BRelation<K,V>();\n" + 
						"			res.addAll(this);\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ 	also \n" + 
						"		 	requires !(obj instanceof BSet);\n" + 
						"			assignable \\nothing;\n" + 
						"		    ensures \\result <==> false;\n" + 
						"		    	also \n" + 
						"		    requires obj instanceof BSet;\n" + 
						"		    assignable \\nothing;\n" + 
						"		    ensures \\result <==> (\\forall Pair<K, V> pair; this.has(pair) <==> ((BSet) obj).has(pair));  \n" + 
						"		 */\n" + 
						"		public /*@ pure */ boolean equals(Object obj) {\n" + 
						"			if (obj instanceof ID) {\n" + 
						"				return false;\n" + 
						"			} else if (obj instanceof BRelation) {\n" + 
						"				BRelation<K, V> rel = (BRelation<K, V>) obj;\n" + 
						"				return super.equals(rel); \n" + 
						"			} else if (obj instanceof BSet) {\n" + 
						"				try {\n" + 
						"					BSet<Pair<K, V>> set = (BSet<Pair<K, V>>) obj;\n" + 
						"					if (set.size() == int_size()) {\n" + 
						"						for (Pair<K, V> pair : set) {\n" + 
						"							if (!has(pair)) return false;\n" + 
						"						}\n" + 
						"						return true;\n" + 
						"					}\n" + 
						"				} catch (ClassCastException cse) {\n" + 
						"					return false;\n" + 
						"				}\n" + 
						"			}\n" + 
						"			return false;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ also \n" + 
						"		    requires true;\n" + 
						"		    assignable \\nothing;\n" + 
						"		    ensures \\result == this.hashCode();\n" + 
						"		 */\n" + 
						"		public /*@ pure */ int hashCode() {\n" + 
						"			return super.hashCode();\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		    assignable \\nothing;\n" + 
						"		    ensures (\\forall K key; \\result.has(key) <==> this.isDefinedAt(key));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ BSet<K> domain() {\n" + 
						"			BSet<K> res = new BSet<K>();\n" + 
						"			for(Pair<K,V> pair : this) {\n" + 
						"				res.add(pair.fst());\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures (\\forall V value; \\result.has(value) <==> (\\exists K key; this.has(key, value)));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ BSet<V> range() {\n" + 
						"			BSet<V> res = new BSet<V>();\n" + 
						"			for(Pair<K,V> pair : this) {\n" + 
						"				res.insertInPlace(pair.snd());\n" + 
						"			}			\n" + 
						"			return res;\n" + 
						"		}		\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable this.*;\n" + 
						"		 	ensures ! \\result.has(pair);\n" + 
						"		 */\n" + 
						"		public BRelation<K, V> delete(Pair<K,V> pair) {			\n" + 
						"			BRelation<K,V> res = new BRelation<K,V>();\n" + 
						"\n" + 
						"			for(Pair<K,V> p : this) {\n" + 
						"				if(!pair.equals(p))\n" + 
						"					res.insertInPlace(p);\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}		\n" + 
						"\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable this.*;\n" + 
						"		 	ensures ! this.has(new Pair<K,V>(key,value));\n" + 
						"		 */\n" + 
						"		public BRelation<K, V> delete(K key, V value) {\n" + 
						"			return delete(new Pair<K,V>(key,value));\n" + 
						"		}\n" + 
						"		\n" + 
						"		public boolean remove(Object obj) {\n" + 
						"			if (obj instanceof Pair) {\n" + 
						"				Pair<K,V> pair = (Pair<K,V>) obj;\n" + 
						"				return super.remove(pair);\n" + 
						"			}\n" + 
						"			return false;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"	 		assignable this.*;\n" + 
						"	 		ensures ! this.has(new Pair<K,V>(key,value));\n" + 
						"		 */\n" + 
						"		public boolean remove(K key, V value) {\n" + 
						"			return remove(new Pair<K,V>(key,value));\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures (\\forall Pair<D, V> rp; \\result.has(rp) <==>\n" + 
						"		      (\\exists Pair<K, V> tp; this.has(tp);\n" + 
						"		        (\\exists Pair<D, K> op; otherRel.has(op);\n" + 
						"		          op.snd().equals(tp.fst()) && rp.snd().equals(tp.snd()) && tp.fst().equals(op.fst()))));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ <D> BRelation<D, V> compose(BRelation<D, K> otherRel) {\n" + 
						"			if (otherRel instanceof ID) {\n" + 
						"				return (BRelation<D, V>) this;\n" + 
						"			} else {\n" + 
						"				BRelation<D, V> res = new BRelation<D, V>();\n" + 
						"				for (Pair<D, K> pair : otherRel) {\n" + 
						"					for (V val : elementImage(pair.snd())) {\n" + 
						"						res.add(pair.fst(), val);\n" + 
						"					}\n" + 
						"				}\n" + 
						"				return res;\n" + 
						"			}\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures (\\forall Pair<K, V> pair; \\result.has(pair) <==>\n" + 
						"		      this.has(pair) || otherRel.has(pair));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ BRelation<K, V> union(BSet<Pair<K, V>> otherRel) {\n" + 
						"			if (otherRel instanceof ID) {\n" + 
						"				throw new UnsupportedOperationException(\"Error: cannot union with the identity relation.\");\n" + 
						"			}\n" + 
						"			BRelation<K,V> res = new BRelation<K,V>();\n" + 
						"			res.addAll(this);\n" + 
						"			res.addAll(otherRel);\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures (\\forall Pair<K, V> e; \\result.has(e) <==>\n" + 
						"	          (\\exists int i; 0 <= 1 && i < sets.length; sets[i].has(e)));\n" + 
						"	     */\n" + 
						"		public /*@ pure */ static <K, V> BRelation<K, V> union(BRelation<K, V> ... sets) {\n" + 
						"			BRelation<K, V> res = new BRelation<K, V>();\n" + 
						"			for (BRelation<K, V> set : sets) {\n" + 
						"				res.unionInPlace(set);\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures (\\forall Pair<K, V> pair; \\result.has(pair) <==>\n" + 
						"	          this.has(pair) && otherRel.has(pair));\n" + 
						"	     */\n" + 
						"		public /*@ pure */ BRelation<K, V> intersection(BSet<Pair<K, V>> otherRel) {\n" + 
						"			if (otherRel instanceof ID) {\n" + 
						"				return ((ID) otherRel).intersection(this);\n" + 
						"			}\n" + 
						"			BRelation<K, V> res = new BRelation<K, V>();\n" + 
						"			for (Pair<K, V> pair : otherRel) {\n" + 
						"				if (this.has(pair)) {\n" + 
						"					res.add(pair);\n" + 
						"				}\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures (\\forall Pair<K, V> e; \\result.has(e) <==>\n" + 
						"	          (\\forall int i; 0 <= 1 && i < sets.length; sets[i].has(e)));\n" + 
						"	     */\n" + 
						"		public /*@ pure */ static <K, V> BRelation<K, V> intersection(BRelation<K, V> ... sets) {\n" + 
						"			BRelation<K, V> res = sets[0];\n" + 
						"			for (int i = 1; i < sets.length; i++) {\n" + 
						"				res.intersectionInPlace(sets[i]);\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures (\\forall Pair<K, V> pair; \\result.has(pair) <==>\n" + 
						"	          this.has(pair) && !otherRel.has(pair));\n" + 
						"	     */\n" + 
						"		public /*@ pure */ BRelation<K, V> difference(BSet<Pair<K, V>> otherRel) {\n" + 
						"			BRelation<K, V> res = new BRelation<K,V>();\n" + 
						"			res.addAll(this);\n" + 
						"			\n" + 
						"			for (Pair<K, V> pair : otherRel) \n" + 
						"				res.remove(pair);\n" + 
						"				\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ also \n" + 
						"		 	  requires true;\n" + 
						"		 	  assignable \\nothing;\n" + 
						"		      ensures \\result.equals(this.toString());\n" + 
						"		 */\n" + 
						"		public /*@ pure */ String toString() {\n" + 
						"			return super.toString();\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result.equals(this.associations());\n" + 
						"	     */\n" + 
						"		public /*@ pure @*/ Iterator<Pair<K, V>> associations() {\n" + 
						"			return super.iterator();\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ also\n" + 
						"		  	  requires true;\n" + 
						"		 	  assignable \\nothing;\n" + 
						"	          ensures \\result.equals(this.iterator());\n" + 
						"	     */\n" + 
						"	    public /*@ pure */ Iterator<Pair<K,V>> iterator() {\n" + 
						"	    	return super.iterator();\n" + 
						"	    }\n" + 
						"	    \n" + 
						"	    /*@ requires true;\n" + 
						"	     	assignable \\nothing;\n" + 
						"	        ensures (\\forall Pair<K, V> pair;\n" + 
						"	          \\result.has(pair) <==> this.has(pair));\n" + 
						"	     */\n" + 
						"	    public /*@ pure non_null @*/ BSet<Pair<K, V>> toSet() {\n" + 
						"	    	BSet<Pair<K, V>> res = new BSet<Pair<K, V>>();\n" + 
						"			for(Pair<K,V> pair : this) {\n" + 
						"				res.add(pair);\n" + 
						"			}\n" + 
						"	    	return res;\n" + 
						"	    }\n" + 
						"	    \n" + 
						"	    /*@ requires true;\n" + 
						"	     	assignable \\nothing;\n" + 
						"	        ensures (\\forall Pair<K, BSet<V>> pair; \\result.has(pair); \n" + 
						"	           this.isDefinedAt(pair.fst()) && pair.snd().equals(this.elementImage(pair.fst())));\n" + 
						"	      */\n" + 
						"	    public /*@ pure non_null @*/ BSet<Pair<K, BSet<V>>> imagePairSet() {\n" + 
						"	    	BSet<K> domain = domain();\n" + 
						"	    	BSet<Pair<K, BSet<V>>> res = new BSet<Pair<K, BSet<V>>>();\n" + 
						"	    	\n" + 
						"	    	for ( K key : domain) {\n" + 
						"	    		Pair<K, BSet<V>> pair = new Pair<K, BSet<V>>(key,elementImage(key));\n" + 
						"	    		res.add(pair);\n" + 
						"	    	}\n" + 
						"	    	return res;\n" + 
						"	    }\n" + 
						"	    \n" + 
						"	    /*@ requires true;\n" + 
						"	     	assignable \\nothing;\n" + 
						"	        ensures \\result.equals(this.imagePairs());\n" + 
						"	     */\n" + 
						"	    public /*@ pure non_null @*/Iterator<Pair<K,V>> imagePairs() {\n" + 
						"	    	return super.iterator();\n" + 
						"	    }\n" + 
						"	    \n" + 
						"	    /*@ requires true;\n" + 
						"	     	assignable \\nothing;\n" + 
						"	        ensures \\result.equals(this.domainElements());\n" + 
						"	     */\n" + 
						"	    public /*@ pure non_null @*/ Iterator<K> domainElements() {\n" + 
						"	    	return domain().iterator();\n" + 
						"	    }\n" + 
						"	    \n" + 
						"	    /*@ requires true;\n" + 
						"	     	assignable \\nothing;\n" + 
						"	        ensures \\result.equals(this.rangeElements());\n" + 
						"	     */\n" + 
						"	    public /*@ pure non_null @*/ Iterator<V> rangeElements() {\n" + 
						"	    	return range().iterator();\n" + 
						"	    }\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures (\\forall Pair<K, V> pair; \n" + 
						"	          \\result.has(pair) <==> this.has(pair) && dom.has(pair.fst()))\n" + 
						"	       && \\result.domain().equals(dom.intersection(this.domain()))\n" + 
						"	       && (\\forall V value; \\result.range().has(value) <==>\n" + 
						"	           (\\exists K k; dom.has(k); this.has(k, value)));\n" + 
						"	    */\n" + 
						"		public /*@ pure */ BRelation<K, V> restrictDomainTo(BSet<K> dom) {\n" + 
						"			BRelation<K,V> res = new BRelation<K,V>();\n" + 
						"			for(Pair<K,V> pair : this) {\n" + 
						"				if (dom.has(pair.fst())) \n" + 
						"					res.add(pair);\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures (\\forall Pair<K, V> pair; \n" + 
						"	          \\result.has(pair) <==> this.has(pair) && ran.has(pair.snd()))\n" + 
						"	       && \\result.range().equals(ran.intersection(this.range()))\n" + 
						"	       && (\\forall K k; \\result.domain().has(k) <==>\n" + 
						"	         (\\exists V v; ran.has(v); this.has(k, v)));\n" + 
						"	    */\n" + 
						"		public /*@ pure */ BRelation<K, V> restrictRangeTo(BSet<V> ran) {\n" + 
						"			BRelation<K,V> res = new BRelation<K,V>();\n" + 
						"			for(Pair<K,V> pair : this) {\n" + 
						"				if (ran.has(pair.snd())) \n" + 
						"					res.add(pair);\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"	    \n" + 
						"	    /*@ requires true;\n" + 
						"	     	assignable \\nothing;\n" + 
						"	        ensures \\result.equals(this.toFunction());\n" + 
						"	     */\n" + 
						"	    public /*@ pure */ BRelation<K,V> toFunction() {\n" + 
						"	    	return restrictDomainTo(domain());\n" + 
						"	    }\n" + 
						"	    \n" + 
						"	    /*@ requires true;\n" + 
						"	     	assignable \\nothing;\n" + 
						"	        ensures \\result.equals(this.restrictDomainTo(this.domain().difference(domain)));\n" + 
						"	     */\n" + 
						"	    public /*@ pure */ BRelation<K, V> domainSubtraction(BSet<K> domain) {\n" + 
						"	    	return restrictDomainTo(domain().difference(domain));\n" + 
						"	    }\n" + 
						"	    \n" + 
						"	    /*@ requires true;\n" + 
						"	     	assignable \\nothing;\n" + 
						"	        ensures \\result.equals(restrictRangeTo(range().difference(range)));\n" + 
						"	     */\n" + 
						"	    public /*@ pure */ BRelation<K, V> rangeSubtraction(BSet<V> range) {\n" + 
						"	    	return restrictRangeTo(range().difference(range));\n" + 
						"	    }\n" + 
						"	    \n" + 
						"	    /*@ requires true;\n" + 
						"	     	assignable \\nothing;\n" + 
						"	        ensures \\result.equals(otherRel.compose(this));\n" + 
						"	     */\n" + 
						"		public /*@ pure */ <D> BRelation<K, D> backwardCompose(BRelation<V, D> otherRel) {\n" + 
						"			return otherRel.compose(this);\n" + 
						"		}\n" + 
						"\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures \\result.equals(other.union(domainSubtraction(other.domain())));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ BRelation<K, V> override(BRelation<K, V> other) {\n" + 
						"			return other.union(domainSubtraction(other.domain()));\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures (\\forall Pair<K, Pair<V, D>> pair; \\result.has(pair) <==>\n" + 
						"		       (\\exists Pair<K, V> tp; this.has(tp);\n" + 
						"		         (\\exists Pair<K, D> op; other.has(op);\n" + 
						"		           tp.fst().equals(op.fst()) && tp.fst().equals(pair.fst()) && \n" + 
						"		             pair.snd().equals(new Pair<V, D>(tp.snd(), op.snd())))));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ <D> BRelation<K, Pair<V, D>> parallel(BRelation<K, D> other) {\n" + 
						"			BRelation<K, Pair<V, D>> res = new BRelation<K, Pair<V, D>>();\n" + 
						"			\n" + 
						"			for(Pair<K,V> pair : this) {\n" + 
						"				for (D val : other.elementImage(pair.fst())) {\n" + 
						"					res.add(pair.fst(), new Pair<V, D>(pair.snd(), val));\n" + 
						"				}\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures (\\forall Pair<Pair<K, K1>, Pair<V, V1>> pair;\n" + 
						"		      \\result.has(pair) <==> this.has(pair.fst()) && other.has(pair.snd()));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ <K1, V1> BRelation<Pair<K, K1>, Pair<V, V1>> directProd(BRelation<K1, V1> other) {\n" + 
						"			BRelation<Pair<K, K1>, Pair<V, V1>> res = new BRelation<Pair<K, K1>, Pair<V, V1>>();\n" + 
						"			\n" + 
						"			for(Pair<K,V> pair : this) {\n" + 
						"				for (Pair<K1, V1> pair2 : other) {\n" + 
						"					res.add(new Pair<K, K1>(pair.fst(), pair2.fst()),\n" + 
						"							      new Pair<V, V1>(pair.snd(), pair2.snd()));\n" + 
						"				}\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"	    \n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures \\result <==> dom.equals(domain()) && range().isSubset(ran);\n" + 
						"		 */\n" + 
						"	    public /*@ pure */ boolean isTotal(BSet<K> dom, BSet<V> ran) {\n" + 
						"	    	return dom.equals(domain()) && range().isSubset(ran);\n" + 
						"	    }\n" + 
						"		\n" + 
						"	    \n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result <==> domain().isSubset(dom) && ran.equals(range());\n" + 
						"	    */\n" + 
						"	    public /*@ pure */ boolean isSurjective(BSet<K> dom, BSet<V> ran) {\n" + 
						"	    	return domain().isSubset(dom) && ran.equals(range());\n" + 
						"		}	\n" + 
						"	    \n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result <==> isTotal(dom, ran) && isSurjective(dom, ran);\n" + 
						"	     */\n" + 
						"	    public /*@ pure */ boolean isTotalSurjective(BSet<K> dom, BSet<V> ran) {\n" + 
						"	    	return isTotal(dom, ran) && isSurjective(dom, ran);\n" + 
						"	    }\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result <==> isaFunction() && isRelation(dom, ran);\n" + 
						"	     */\n" + 
						"		public /*@ pure */ boolean isFunction(BSet<K> dom, BSet<V> ran) {\n" + 
						"			return isaFunction() && isRelation(dom, ran);\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result <==> domain().isSubset(dom) && range().isSubset(ran);\n" + 
						"	     */\n" + 
						"		public /*@ pure */ boolean isRelation(BSet<K> dom, BSet<V> ran) {\n" + 
						"			return domain().isSubset(dom) && range().isSubset(ran);\n" + 
						"		}\n" + 
						"\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result <==> isaFunction() && isTotal(dom, ran) && range().isSubset(ran);\n" + 
						"	     */\n" + 
						"		public /*@ pure */ boolean isTotalFunction(BSet<K> dom, BSet<V> ran) {\n" + 
						"			return isaFunction() && isTotal(dom, ran) && range().isSubset(ran);\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result <==> isaFunction() && inverse().isaFunction() && isRelation(dom, ran);\n" + 
						"	     */\n" + 
						"		public /*@ pure */ boolean isPartialInjection(BSet<K> dom, BSet<V> ran) {\n" + 
						"			return isaFunction() && inverse().isaFunction() && isRelation(dom, ran);			\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result <==> isPartialInjection(dom, ran) && isTotal(dom, ran);\n" + 
						"	     */\n" + 
						"		public /*@ pure */ boolean isTotalInjection(BSet<K> dom, BSet<V> ran) {\n" + 
						"			return isPartialInjection(dom, ran) && isTotal(dom, ran);\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result <==> isaFunction() && isSurjective(dom, ran);\n" + 
						"	     */\n" + 
						"		public /*@ pure */ boolean isPartialSurjection(BSet<K> dom, BSet<V> ran) {\n" + 
						"			return isaFunction() && isSurjective(dom, ran);\n" + 
						"		}\n" + 
						"\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result <==> isTotalFunction(dom, ran) && isPartialSurjection(dom, ran);\n" + 
						"	     */\n" + 
						"		public /*@ pure */ boolean isTotalSurjection(BSet<K> dom, BSet<V> ran) {\n" + 
						"			return isTotalFunction(dom, ran) && isPartialSurjection(dom, ran);\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result <==> isPartialInjection(dom, ran) && isPartialSurjection(dom, ran);\n" + 
						"	     */\n" + 
						"		public /*@ pure */ boolean isInjection(BSet<K> dom, BSet<V> ran) {\n" + 
						"			return isPartialInjection(dom, ran) && isPartialSurjection(dom, ran);\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ public normal_behavior\n" + 
						"		      requires this.isaFunction();\n" + 
						"		      assignable \\nothing;\n" + 
						"		      ensures \\result.equals(this.elementImage(key).choose());\n" + 
						"		    also public exceptional_behavior\n" + 
						"		      requires !this.isaFunction();\n" + 
						"		      assignable \\nothing;\n" + 
						"		      signals (IllegalStateException);\n" + 
						"		 */\n" + 
						"		public /*@ pure */ V apply(K key) {\n" + 
						"			//return elementImage(key).choose();\n" + 
						"			for(Pair<K,V> p : this) {\n" + 
						"				if(p.fst().equals(key))\n" + 
						"					return p.snd();\n" + 
						"			}\n" + 
						"			return null;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ also \n" + 
						"		 	requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures (\\forall BSet<Pair<K, V>> s; \\result.has(s) <==> s.isSubset(this));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ BSet<BSet<Pair<K, V>>> pow() {\n" + 
						"			return super.pow();\n" + 
						"		}\n" + 
						"			\n" + 
						"		/*@ also \n" + 
						"		 	requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures (\\forall BSet<Pair<K, V>> s; \\result.has(s) <==> s.isSubset(this) && !s.isEmpty());\n" + 
						"	     */\n" + 
						"		public /*@ pure */ BSet<BSet<Pair<K, V>>> pow1() {\n" + 
						"			return super.pow1();\n" + 
						"		}\n" + 
						"\n" + 
						"	    /*@ requires true;\n" + 
						"	     	assignable \\nothing;\n" + 
						"	        ensures \\result <==> (\\forall Pair<K, V> e; c.contains(e); this.has(e));\n" + 
						"	     */\n" + 
						"		public /*@ pure */ boolean containsAll(java.util.Collection<?> c) {\n" + 
						"			return super.containsAll(c);\n" + 
						"		}\n" + 
						"		\n" + 
						"	    /*@ requires true;\n" + 
						"	     	assignable \\nothing;\n" + 
						"	        ensures \\result <==> (\\forall Pair<K, V> e; this.has(e); other.has(e));\n" + 
						"	     */\n" + 
						"		public /*@ pure */ boolean isSubset(BSet<Pair<K, V>> other) {	\n" + 
						"			for(Pair<K,V> pair : this) {\n" + 
						"				if (!other.has(pair)) return false;\n" + 
						"			}\n" + 
						"			return true;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"	        ensures \\result <==> this.isSubset(other) && !this.equals(other);\n" + 
						"		 */\n" + 
						"		public /*@ pure */ boolean isProperSubset(BSet<Pair<K, V>> other) {\n" + 
						"			return this.isSubset(other) && !this.equals(other);\n" + 
						"		}\n" + 
						"				\n" + 
						"		public /*@ pure */ Pair<K, V> choose() {\n" + 
						"			if(isSingleton())\n" + 
						"				throw new IllegalStateException(\"Error: no elements in an empty set\");\n" + 
						"			return super.choose();\n" + 
						"		}\n" + 
						"\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures \\result <==> true;\n" + 
						"		 */\n" + 
						"		public /*@ pure */ boolean finite() {\n" + 
						"			return true;\n" + 
						"		}\n" + 
						"		\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures \\result <==> false;\n" + 
						"		 */\n" + 
						"		public /*@ pure */ boolean infinite() {\n" + 
						"			return false;\n" + 
						"		}\n" + 
						"\n" + 
						"		/*@ requires true;\n" + 
						"		 	assignable \\nothing;\n" + 
						"		    ensures (\\forall Pair<K, V> e; \\result.has(e) <==>\n" + 
						"		      domain.has(e.fst()) && range.has(e.snd()));\n" + 
						"		 */\n" + 
						"		public /*@ pure */ static <K, V> BRelation<K, V> cross(BSet<K> domain, BSet<V> range) {\n" + 
						"			BRelation<K, V> res = new BRelation<K, V>();\n" + 
						"			for (K key : domain) {\n" + 
						"				for (V value : range) {\n" + 
						"					res.add(key, value);\n" + 
						"				}\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"\n" + 
						"}";

		String BSet =
				"package eventb_prelude;\n" + 
						"\n" + 
						"/** a class to model B sets in Java \n" + 
						" * @author Tim Wahls & Nestor Catano & Victor Rivera\n" + 
						" */\n" + 
						"\n" + 
						"import java.util.Iterator;\n" + 
						"import java.util.TreeSet;\n" + 
						"//@model import org.jmlspecs.models.JMLIterator;\n" + 
						"//@model import org.jmlspecs.models.JMLObjectSet;\n" + 
						"\n" + 
						"public class BSet<E> extends TreeSet<E> implements Comparable<E> {\n" + 
						"\n" + 
						"	/*@ public static invariant EMPTY.int_size() == 0; */\n" + 
						"\n" + 
						"	public static BSet EMPTY = new BSet();\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result != null && \\result.int_size() == 1 && \\result.has(elem);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ static <EE> BSet<EE> singleton(EE elem) {\n" + 
						"		BSet<EE> res = new BSet<EE>();\n" + 
						"		res.add(elem);\n" + 
						"		return res;\n" + 
						"	}\n" + 
						"	\n" + 
						"	/*@ public model BSet(JMLObjectSet S){\n" + 
						"			this();\n" + 
						"			JMLIterator iter = S.iterator();\n" + 
						"			while (iter.hasNext()){\n" + 
						"				add((E) iter.next());\n" + 
						"			}\n" + 
						"		}*/\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	  	ensures \\result == this.size();\n" + 
						"	 */\n" + 
						"	public /*@ pure */ int int_size(){\n" + 
						"		return this.size();\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result <==> this.has(obj);\n" + 
						"	*/\n" + 
						"	public /*@ pure */ boolean has(Object obj) {\n" + 
						"		return contains(obj);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result <==> this.int_size() == 1;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isSingleton(){\n" + 
						"		return (size() == 1);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures this.isEmpty();\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BSet() {	}\n" + 
						"		\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable this.*;\n" + 
						"	 	ensures (\\forall int i; i >= 0 && i < elems.length ==> this.has(elems[i]));\n" + 
						"	 */\n" + 
						"	public BSet(E ... elems) {\n" + 
						"		this();\n" + 
						"		for (E e : elems) {\n" + 
						"			add(e);\n" + 
						"		}\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable this.*;\n" + 
						"	 	ensures (\\forall E e; elems.contains(e) ==> this.has(e));\n" + 
						"	*/\n" + 
						"	public BSet(TreeSet<E> elems) {\n" + 
						"		this();\n" + 
						"		for (E e : elems)\n" + 
						"			add(e);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result.equals(this.insert(elem));\n" + 
						"	*/\n" + 
						"	public /*@ pure */ BSet<E> insert(E elem) {\n" + 
						"		BSet<E> res = new BSet<E>();\n" + 
						"		res.addAll(this);\n" + 
						"\n" + 
						"		res.add(elem);\n" + 
						"		return res;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable this.*;\n" + 
						"	 	ensures this.equals(\\old(this).insert(elem));\n" + 
						"	*/\n" + 
						"	public void insertInPlace(E elem) {\n" + 
						"		add(elem);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures !\\result.contains(elem);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BSet<E> delete(E elem) {\n" + 
						"		BSet<E> res = new BSet<E>();\n" + 
						"		for(E e : this)\n" + 
						"			if(!e.equals(elem))\n" + 
						"				res.add(e);\n" + 
						"		return res;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable this.*;\n" + 
						"	 	ensures !this.contains(elem);\n" + 
						"	 */\n" + 
						"	public void deleteInPlace(E elem) {\n" + 
						"		remove(elem);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result <==> (\\forall E e; c.contains(e); this.has(e));\n" + 
						"	*/\n" + 
						"	public /*@ pure */ boolean containsAll(java.util.Collection<?> c) {\n" + 
						"		return super.containsAll(c);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ 	also\n" + 
						"	  	requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"    	  ensures \\result <==> obj instanceof BSet && \n" + 
						"              (\\forall E e; ((BSet) obj).has(e) <==> this.has(e));\n" + 
						"    */\n" + 
						"	public /*@ pure */ boolean equals(Object obj) {\n" + 
						"		if (obj instanceof BRelation) {\n" + 
						"			BSet s = ((BRelation) obj).toSet();\n" + 
						"			return(size() == s.size() && containsAll(s) && s.containsAll(this));\n" + 
						"		} \n" + 
						"		else if (obj instanceof BSet) {\n" + 
						"			BSet s = (BSet) obj;\n" + 
						"\n" + 
						"			return(size() == s.size() && containsAll(s) && s.containsAll(this));\n" + 
						"		}\n" + 
						"		else return false;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result <==> (\\forall E e; this.has(e); s2.contains(e));\n" + 
						"	*/\n" + 
						"	public /*@ pure */ boolean isSubset(TreeSet<E> s2) {\n" + 
						"		if (s2 instanceof INT) {\n" + 
						"			return true;\n" + 
						"		} else if (s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"			for (Object obj : this) {\n" + 
						"				Integer i = (Integer) obj;\n" + 
						"				if (i < 0) return false;\n" + 
						"				else if (i == 0 && s2 instanceof NAT1) return false;\n" + 
						"			}\n" + 
						"			return true;\n" + 
						"		} else {\n" + 
						"			return s2.containsAll(this);\n" + 
						"		}\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result <==> this.isSubset(s2) && !this.equals(s2);\n" + 
						"	*/\n" + 
						"	public /*@ pure */ boolean isProperSubset(BSet<E> s2) {\n" + 
						"		if (s2 instanceof INT || s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"			return isSubset(s2);\n" + 
						"		} else {\n" + 
						"			return s2.containsAll(this) && !this.containsAll(s2);\n" + 
						"		}\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result <==> s2.isSubset(this);\n" + 
						"	*/\n" + 
						"	public /*@ pure */ boolean isSuperset(BSet<E> s2) {\n" + 
						"		return s2.isSubset(this);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result <==> s2.isProperSubset(this);\n" + 
						"	*/\n" + 
						"	public /*@ pure */ boolean isProperSuperset(BSet<E> s2) {\n" + 
						"		return s2.isProperSubset(this);\n" + 
						"	}\n" + 
						"\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	  	assignable \\nothing;\n" + 
						"	  	ensures \\result.equals(this.first());\n" + 
						"	 */\n" + 
						"	public /*@ pure */ E choose() {\n" + 
						"		//return iterator().next();\n" + 
						"		return first();\n" + 
						"	}\n" + 
						"	\n" + 
						"	/*@	requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures (\\forall E e; \\result.has(e) <==> this.has(e) || s2.contains(e));\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BSet<E> union(TreeSet<E> s2) {\n" + 
						"		if (s2 instanceof INT) {\n" + 
						"			return (BSet<E>) s2;\n" + 
						"		} else if (s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"			for (Object obj : this) {\n" + 
						"				Integer i = (Integer) obj;\n" + 
						"				if (i < 0) throw new UnsupportedOperationException(\"Error: can't union with NAT.\");\n" + 
						"				else if (i == 0 && s2 instanceof NAT1) throw new UnsupportedOperationException(\"Error: can't union with NAT1.\");\n" + 
						"			}\n" + 
						"			return (BSet<E>) s2;\n" + 
						"		} else {\n" + 
						"			BSet<E> res = new BSet<E>();\n" + 
						"			res.addAll(this);\n" + 
						"\n" + 
						"			for (E e : s2)\n" + 
						"				res.add(e);\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable this.*;\n" + 
						"	 	ensures this.equals(\\old(this).union(s2));\n" + 
						"	 */\n" + 
						"	public void unionInPlace(TreeSet<E> s2) {\n" + 
						"		if (s2 instanceof INT) {\n" + 
						"			clear();\n" + 
						"			addAll(s2);\n" + 
						"		} else if (s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"			for (Object obj : this) {\n" + 
						"				Integer i = (Integer) obj;\n" + 
						"				if (i < 0) throw new UnsupportedOperationException(\"Error: can't union with NAT.\");\n" + 
						"				else if (i == 0 && s2 instanceof NAT1) throw new UnsupportedOperationException(\"Error: can't union with NAT1.\");\n" + 
						"			}\n" + 
						"			clear();\n" + 
						"			addAll(s2);\n" + 
						"		} else {				\n" + 
						"			for (E e : s2)\n" + 
						"				add(e);\n" + 
						"		}\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	  	assignable \\nothing;\n" + 
						"	  	ensures \\result.isEmpty();\n" + 
						"	*/\n" + 
						"	public /*@ pure */ static <E> BSet<E> union() {\n" + 
						"		return new BSet<E>();\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@	requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures (\\forall E e; \\result.has(e) <==>\n" + 
						"					(\\exists int i; 0 <= 1 && i < sets.length; sets[i].has(e)));\n" + 
						"	*/\n" + 
						"	public /*@ pure */ static <E> BSet<E> union(BSet<E> ... sets) {\n" + 
						"		BSet<E> res = new BSet<E>();\n" + 
						"		for (BSet<E> set : sets) {\n" + 
						"			res.unionInPlace(set);\n" + 
						"		}\n" + 
						"		return res;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures (\\forall E e; \\result.has(e) <==> \n" + 
						"					(\\exists int i; 0 <= 1 && i < elems.length; elems[i].equals(e)));*/\n" + 
						"	public /*@ pure */ static <E> BSet<E> extension(E ... elems) {\n" + 
						"		BSet<E> res = new BSet<E>();\n" + 
						"		for (E e : elems) {\n" + 
						"			res.add(e);\n" + 
						"		}\n" + 
						"		return res;\n" + 
						"	}	\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures (\\forall E e; \\result.has(e) <==> this.has(e) && s2.contains(e));*/\n" + 
						"	public /*@ pure */ BSet<E> intersection(TreeSet<E> s2) {\n" + 
						"		if (s2 instanceof INT) {\n" + 
						"			BSet<E> res = (BSet<E>) clone();\n" + 
						"			return res;\n" + 
						"		} else if (s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"			BSet<E> res = (BSet<E>) clone();\n" + 
						"			for (E obj : this) {\n" + 
						"				Integer i = (Integer) obj;\n" + 
						"				if (i < 0) res.remove(obj);\n" + 
						"				else if (i == 0 && s2 instanceof NAT1) res.remove(obj);				\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		} else {\n" + 
						"			BSet<E> res = new  BSet<E>(); // the empty set\n" + 
						"\n" + 
						"			for (E e : s2) { \n" + 
						"				if (contains(e)) {\n" + 
						"					res.add(e);\n" + 
						"				}\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures (\\forall E e; this.has(e) <==> \\old(this).has(e) && s2.contains(e));*/\n" + 
						"	public /*@ pure */ void intersectionInPlace(TreeSet<E> s2) {\n" + 
						"		if (s2 instanceof INT) {\n" + 
						"			//\n" + 
						"		} else if (s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"			for (E obj : this) {\n" + 
						"				Integer i = (Integer) obj;\n" + 
						"				if (i < 0) remove(obj);\n" + 
						"				else if (i == 0 && s2 instanceof NAT1) remove(obj);				\n" + 
						"			}\n" + 
						"		} else {\n" + 
						"			clear(); //TODO why clear?\n" + 
						"			for (E e : s2) { \n" + 
						"				if (contains(e))\n" + 
						"					add(e);\n" + 
						"			}\n" + 
						"		}\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@	requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures (\\forall E e; \\result.has(e) <==>\n" + 
						"          (\\forall int i; 0 <= 1 && i < sets.length; sets[i].has(e)));\n" + 
						"    */\n" + 
						"	public /*@ pure */ static <E> BSet<E> intersection(BSet<E> ... sets) {\n" + 
						"		BSet<E> res = sets[0];\n" + 
						"		for (int i = 1; i < sets.length; i++) {\n" + 
						"			res.intersectionInPlace(sets[i]);\n" + 
						"		}\n" + 
						"		return res;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ public exceptional_behavior\n" + 
						"	 	requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    signals (IllegalStateException);\n" + 
						"	*/\n" + 
						"	public /*@ pure */ static <E> BSet<E> intersection() {\n" + 
						"		throw new IllegalStateException(\"Error: generalized intersection over 0 sets.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures (\\forall E e; \\result.has(e) <==> this.has(e) && !s2.contains(e));\n" + 
						"	*/\n" + 
						"	public /*@ pure */ BSet<E> difference(TreeSet<E> s2) {\n" + 
						"		if (s2 instanceof INT) {\n" + 
						"			return new BSet<E>(); // the empty set\n" + 
						"		} else if (s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"			BSet<E> res = (BSet<E>) clone();\n" + 
						"			for (E obj : this) {\n" + 
						"				Integer i = (Integer) obj;\n" + 
						"				if (i > 0) res.remove(obj);\n" + 
						"				else if (i == 0 && s2 instanceof NAT) res.remove(obj);\n" + 
						"			}\n" + 
						"			return res;\n" + 
						"		} else {\n" + 
						"			BSet<E> res = (BSet<E>) clone();\n" + 
						"\n" + 
						"			for (E e : s2) \n" + 
						"				if (has(e)) res.remove(e);\n" + 
						"			return res;\n" + 
						"		}\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable this.*;\n" + 
						"	 	ensures (\\forall E i; s2.contains(i) ==> !this.has(i));\n" + 
						"	 */\n" + 
						"	public void differenceInPlace(TreeSet<E> s2) {\n" + 
						"		if (s2 instanceof INT) {\n" + 
						"			clear(); // the empty set\n" + 
						"		} else if (s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"			for (E obj : this) {\n" + 
						"				Integer i = (Integer) obj;\n" + 
						"				if (i > 0) remove(obj);\n" + 
						"				else if (i == 0 && s2 instanceof NAT) remove(obj);\n" + 
						"			}\n" + 
						"		} else {			\n" + 
						"			for (E e : s2) \n" + 
						"				if (contains(e)) remove(e);\n" + 
						"		}\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ public exceptional_behavior\n" + 
						"	 	requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"		signals (UnsupportedOperationException);*/\n" + 
						"	public /*@ pure */ TreeSet<TreeSet<E>> powerSet() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: do not call powerSet through a BSet.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also\n" + 
						"	  	requires true;\n" + 
						"	  	assignable \\nothing;\n" + 
						"		ensures \\result.equals(this.toString());*/\n" + 
						"	public /*@ pure */ String toString() {\n" + 
						"		return super.toString();\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also\n" + 
						"	 		requires true;\n" + 
						"	 		assignable \\nothing;\n" + 
						"			ensures \\result.equals(this.toArray());*/\n" + 
						"	public /*@ pure */ Object [] toArray() {\n" + 
						"		return super.toArray();\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also\n" + 
						"	 	requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"		ensures \\result.equals(this.iterator());*/\n" + 
						"	public /*@ pure */ Iterator<E> iterator() {\n" + 
						"		return super.iterator();\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures (\\forall BSet<E> es; \\result.has(es) <==> es.isSubset(this));\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BSet<BSet<E>> pow() {\n" + 
						"		BSet<BSet<E>> ps = new BSet<BSet<E>>();\n" + 
						"		ps.add(new BSet<E>());   // add the empty set \n" + 
						"\n" + 
						"		// for every item in the original set\n" + 
						"		for(E item : this) {	\n" + 
						"			BSet<BSet<E>> newPs = new BSet<BSet<E>>();\n" + 
						"\n" + 
						"			for (BSet<E> subset : ps) {\n" + 
						"				// copy all of the current powerset's subsets\n" + 
						"				newPs.add(subset);\n" + 
						"\n" + 
						"				// plus the subsets appended with the current item\n" + 
						"				BSet<E> newSubset = new BSet<E>(subset);\n" + 
						"				newSubset.add(item);\n" + 
						"				newPs.add(newSubset);\n" + 
						"			}\n" + 
						"			ps = newPs;\n" + 
						"		}\n" + 
						"\n" + 
						"		return ps;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures (\\forall BSet<E> es; \\result.has(es) <==> \n" + 
						"	  				es.isSubset(this) && !es.isEmpty());\n" + 
						"	*/\n" + 
						"	public /*@ pure */ BSet<BSet<E>> pow1() {\n" + 
						"		BSet<BSet<E>> res = pow();\n" + 
						"		BSet<E> empty = new BSet<E>();\n" + 
						"		res.remove(empty);\n" + 
						"\n" + 
						"		return res;\n" + 
						"	}\n" + 
						"\n" + 
						"	/* requires true;\n" + 
						"	 	assignable \\nothing; \n" + 
						"	 	ensures \\result <==> \n" + 
						"	  		!(this instanceof INT || this instanceof NAT || this instanceof NAT1);*/\n" + 
						"	public /*@ pure */ boolean finite() {\n" + 
						"		//TODO to check\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*TODO ensures \\result <==> (\\forall int i; 0 <= i && i < parts.length; \n" + 
						"	!(\\exists int j; 0 <= j && j < parts.length; i != j && !parts[i].intersection(parts[j]).isEmpty()))\n" + 
						"	&& (\\forall E e; this.has(e) <==> (\\exists int i; 0 <= i && i < parts.length; parts[i].has(e)));*/\n" + 
						"	public /*@ pure */ static <E> boolean partition(BSet<E> ... parts) {\n" + 
						"		BSet<E> tmp = new BSet<E>(); // the empty set\n" + 
						"\n" + 
						"		if(parts.length == 0) return false;\n" + 
						"		if(parts.length == 1) return true;\n" + 
						"\n" + 
						"		for(BSet<E> part : parts) {\n" + 
						"			if(!tmp.intersection(part).isEmpty()) return false;\n" + 
						"			tmp.unionInPlace(part);\n" + 
						"		}\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result.equals(last());\n" + 
						"	 */\n" + 
						"	public /*@ pure */ E max() {\n" + 
						"		return last();\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ requires true;\n" +
						"	 	assignable \\nothing;\n" +
						"	 	ensures (\\forall K key; \\result.has(key) <==> this.isDefinedAt(key));da\n"+
						" */\n" +
						"	public <KK,VV> BSet<KK> domain() {\n" +
						"		BSet<KK> res = new BSet<KK>();\n" +
						"		for(E pair : this) {\n" +
						"			Pair<KK,VV> p = (Pair<KK,VV>) pair;\n" +
						"			res.add(p.fst());\n" +
						"		}\n" +
						"		return res;\n" +
						"	}\n" +
						"\n" +
						"	/*@ requires true;\n" +
						"		assignable \\nothing;\n" +
						"		ensures (\\forall V value; \\result.has(value) <==> (\\exists K key; this.has(key, value)));\n" +
						"	*/\n" +
						"	public <KK,VV> BSet<VV> range() {\n" +
						"		BSet<VV> res = new BSet<VV>();\n" +
						"		for(E pair : this) {\n" +
						"			Pair<KK,VV> p = (Pair<KK,VV>) pair;\n" +
						"			res.add(p.snd());\n" +
						"		}\n" +
						"		return res;\n" +
						"	}\n" +
						"\n" +
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result.equals(last());\n" + 
						"	 */\n" + 
						"	public /*@ pure */ E min() {\n" + 
						"		return first();\n" + 
						"	}\n" + 
						"\n" + 
						"	public boolean contains(Object obj) {\n" + 
						"		return super.contains(obj);\n" + 
						"	}\n" + 
						"\n" + 
						"	public int compareTo(Object o) {\n" + 
						"		if(o instanceof BSet) {\n" + 
						"			BSet<E> s = (BSet<E>) o;\n" + 
						"			Iterator<E> i1 = this.iterator();\n" + 
						"            Iterator<E> i2 = ((BSet<E>) o).iterator();\n" + 
						"            while (i1.hasNext() && i2.hasNext()) {\n" + 
						"                int res = ((Comparable<E>) i1.next()).compareTo(i2.next());\n" + 
						"                if (res != 0) return res;\n" + 
						"            }\n" + 
						"            if (i1.hasNext()) return 1;\n" + 
						"            if (i2.hasNext()) return -1;\n" + 
						"            return 0;\n" + 
						"		}\n" + 
						"		throw new UnsupportedOperationException(\"Error: can only compare sets.\");\n" + 
						"	}\n" + 
						"	\n" + 
						"}";

		String Enumerated =
				"package eventb_prelude;\n" + 
						"\n" + 
						"/** Enumerated type in Java\n" + 
						" * @author Tim Wahls & Nestor Catano & Victor Rivera\n" + 
						" */\n" + 
						"\n" + 
						"public class Enumerated extends BSet<Integer> {\n" + 
						"	/*@	requires true;\n" + 
						"	  	assignable this.*;\n" + 
						"	 	ensures (\\forall int i; low <= i && i <= hi; this.has(i)) \n" + 
						"		         				&& this.int_size() == (hi - low) + 1;\n" + 
						"	*/\n" + 
						"	public Enumerated(int low, int hi) {\n" + 
						"		for (int i = low; i <= hi; i++) {\n" + 
						"			add(new Integer(i));\n" + 
						"		}\n" + 
						"	}\n" + 
						"}";

		String ID =
				"package eventb_prelude;\n" + 
						"\n" + 
						"import java.util.Iterator;\n" + 
						"\n" + 
						"/** representation of the Event-B identity relation\n" + 
						" * @author Tim Wahls & Nestor Catano & Victor Rivera\n" + 
						" */\n" + 
						"\n" + 
						"public class ID<E> extends BRelation<E, E> {\n" + 
						"	public ID() {}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isaFunction() {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result.has(key) && \\result.int_size() == 1;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BSet<E> elementImage(E key) {\n" + 
						"		return BSet.singleton(key);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result.equals(keys);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BSet<E> image(BSet<E> keys) {\n" + 
						"		return keys;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"    	ensures \\result.equals(this);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BRelation<E, E> inverse() {\n" + 
						"		return (BRelation) super.clone();\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result.has(value) && \\result.int_size() == 1;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BSet<E> inverseElementImage(E value) {\n" + 
						"		return new BSet<E>(value);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result.equals(values);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BSet<E> inverseImage(BSet<E> values) {\n" + 
						"		return values;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isDefinedAt(E key) {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	      requires true;\n" + 
						"	      assignable \\nothing;\n" + 
						"          signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean add(E key, E value) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot add to the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"          requires true;\n" + 
						"          assignable \\nothing;\n" + 
						"          signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BRelation<E, E> insert(Pair<E, E> pair) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot add to the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	 	  requires true;\n" + 
						"          assignable \\nothing;\n" + 
						"          signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ int int_size() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: the identity relation is infinite.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result <==> key.equals(value);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean has(E key, E value) {\n" + 
						"		return key.equals(value);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result <==> pair.fst().equals(pair.snd());\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean has(Pair<E, E> pair) {\n" + 
						"		return pair.fst().equals(pair.snd());\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result <==> false;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isEmpty() {\n" + 
						"		return false;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires !(obj instanceof ID);\n" + 
						"	      assignable \\nothing;\n" + 
						"	      ensures \\result <==> false;\n" + 
						"	    also requires obj instanceof ID;\n" + 
						"	      assignable \\nothing;\n" + 
						"	      ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean equals(Object obj) {\n" + 
						"		return obj instanceof ID;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result == \"ID\".hashCode();\n" + 
						"	 */\n" + 
						"	public /*@ pure */ int hashCode() {\n" + 
						"		return \"ID\".hashCode();\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"    	requires true;\n" + 
						"    	assignable \\nothing;\n" + 
						"    	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BSet<E> domain() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot find the domain of the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BSet<E> range() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot find the range of the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BRelation<E, E> removeFromDomain(E key) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot remove from the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean remove(E key, E value) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot remove from the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean remove(Pair<E, E> pair) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot remove from the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean remove(Object obj) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot remove from the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result.equals(otherRel);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ <D> BRelation<D, E> compose(BRelation<D, E> otherRel) {\n" + 
						"		return otherRel;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BRelation<E, E> union(BSet<Pair<E, E>> otherRel) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot union with the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures (\\forall Pair<E, E> pair; \\result.has(pair) <==>\n" + 
						"	      otherRel.has(pair) && pair.fst().equals(pair.snd()));\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BRelation<E, E> intersection(BSet<Pair<E, E>> otherRel) {\n" + 
						"		BRelation<E, E> res = new BRelation<E, E>();\n" + 
						"		for (Pair<E, E> pair : otherRel) {\n" + 
						"			if (pair.fst().equals(pair.snd())) {\n" + 
						"				res = res.insert(pair);\n" + 
						"			}\n" + 
						"		}\n" + 
						"		return res;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BRelation<E, E> difference(BSet<Pair<E, E>> otherRel) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot remove from the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures (\\forall E e; dom.has(e); \\result.has(e, e));\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BRelation<E, E> restrictDomainTo(BSet<E> dom) {\n" + 
						"		return BRelation.cross(dom, dom);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures (\\forall E e; ran.has(e); \\result.has(e, e));\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BRelation<E, E> restrictRangeTo(BSet<E> ran) {\n" + 
						"		return BRelation.cross(ran, ran);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result.equals(\"ID\".toString());\n" + 
						"	 */\n" + 
						"	public /*@ pure */ String toString() {\n" + 
						"		return \"ID\";\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"          requires true;\n" + 
						"          assignable \\nothing;\n" + 
						"          signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ non_null @*/ Iterator<Pair<E,E>> associations() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot iterate over the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ Iterator<Pair<E,E>> iterator() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot iterate over the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ non_null @*/ BSet<Pair<E,E>> toSet() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: a set cannot contain the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ non_null @*/ BSet<Pair<E, BSet<E>>> imagePairSet() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot iterate over the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ non_null @*/ Iterator<Pair<E,E>> imagePairs() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot iterate over the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ non_null @*/ Iterator<E> domainElements()\n" + 
						"	{\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot iterate over the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ non_null @*/ Iterator<E> rangeElements()\n" + 
						"	{\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot iterate over the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BRelation<E, E> toFunction() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: a function cannot contain the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BRelation<E, E> domainSubtraction(BSet<E> domain) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot remove from the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BRelation<E, E> rangeSubtraction(BSet<E> range) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot remove from the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isTotal(BSet<E> domain, BSet<E> range) {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isSurjective(BSet<E> domain, BSet<E> range) {\n" + 
						"		return true;\n" + 
						"	}	\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isTotalSurjective(BSet<E> domain, BSet<E> range) {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isFunction(BSet<E> dom, BSet<E> ran) {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isRelation(BSet<E> dom, BSet<E> ran) {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isTotalFunction(BSet<E> dom, BSet<E> ran) {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isPartialInjection(BSet<E> dom, BSet<E> ran) {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isTotalInjection(BSet<E> dom, BSet<E> ran) {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isPartialSurjection(BSet<E> dom, BSet<E> ran) {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isTotalSurjection(BSet<E> dom, BSet<E> ran) {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> true;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean isInjection(BSet<E> dom, BSet<E> ran) {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result.equals(otherRel);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ <D> BRelation<E, D> backwardCompose(BRelation<E, D> otherRel) {\n" + 
						"		return otherRel;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BRelation<E, E> override(BRelation<E, E> other) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot remove from the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ <D> BRelation<E, Pair<E, D>> parallel(BRelation<E, D> other) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot parallel the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ <K1, V1> BRelation<Pair<E, K1>, Pair<E, V1>> directProd(BRelation<K1, V1> other) {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot direct product with the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result.equals(key);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ E apply(E key) {\n" + 
						"		return key;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BSet<BSet<Pair<E, E>>> pow() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot compute powerset of the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ BSet<BSet<Pair<E, E>>> pow1() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot compute powerset of the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result <==> false;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean finite() {\n" + 
						"		return false;\n" + 
						"	}\n" + 
						"\n" + 
						"	/** inherited specs for containsAll, sub and supersets and choose are correct */\n" + 
						"\n" + 
						"	public boolean containsAll(java.util.Collection<?> col) {\n" + 
						"		for (Object obj : col) {\n" + 
						"			if (obj instanceof Pair) {\n" + 
						"				Pair<E,E> pair = (Pair<E,E>) obj;\n" + 
						"				if (!pair.fst().equals(pair.snd())) return false;\n" + 
						"			}\n" + 
						"			else return false;\n" + 
						"		}\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	public boolean isSubset(BSet<Pair<E, E>> other) {\n" + 
						"		if (other instanceof ID) {\n" + 
						"			return true;\n" + 
						"		} else {\n" + 
						"			return false;\n" + 
						"		}\n" + 
						"	}\n" + 
						"\n" + 
						"	public boolean isProperSubset(BSet<Pair<E, E>> other) {\n" + 
						"		return false;\n" + 
						"	}\n" + 
						"\n" + 
						"	public boolean isSuperset(BSet<Pair<E, E>> other) {\n" + 
						"		if (other instanceof ID) return true;\n" + 
						"		for (Pair<E, E> pair : other) {\n" + 
						"			if (!pair.fst().equals(pair.snd())) return false;\n" + 
						"		}\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"\n" + 
						"	public boolean isProperSuperset(BSet<Pair<E, E>> other) {\n" + 
						"		if (other instanceof ID) return false;\n" + 
						"		return isSuperset(other);\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"	 */\n" + 
						"	public /*@ pure */ Pair<E, E> choose() {\n" + 
						"		throw new UnsupportedOperationException(\"Error: cannot choose from the identity relation.\");\n" + 
						"	}\n" + 
						"\n" + 
						"}";

		String INT =
				"package eventb_prelude;\n" + 
						"\n" + 
						"\n" + 
						"/** representation of the EventB type INT as a BSet\n" + 
						" * @author Tim Wahls & Nestor Catano & Victor Rivera\n" + 
						" */\n" + 
						"\n" + 
						"import java.util.ArrayList;\n" + 
						"import java.util.TreeSet;\n" + 
						"import java.util.Iterator;\n" + 
						"\n" + 
						"\n" + 
						"public /*@ pure */ class INT extends BSet<Integer> {\n" + 
						"	public static final INT instance = new INT();\n" + 
						"	private java.util.Random rand = new java.util.Random();\n" + 
						"	\n" + 
						"	/*@ public initially (\\forall int iv; INT.instance.has(iv)); */\n" + 
						"	\n" + 
						"	public INT() {}\n" + 
						"	\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result <==> obj instanceof Integer;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean has(Object obj) {\n" + 
						"		return obj instanceof Integer;\n" + 
						"	}\n" + 
						"	\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result <==> (\\forall Integer i; c.contains(i); this.has(i));\n" + 
						"     */\n" + 
						"	public /*@ pure */ boolean containsAll(java.util.Collection<?> c) {\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"	\n" + 
						"	/*@ also requires other instanceof BSet;\n" + 
						"	    assignable \\nothing;\n" + 
						"        ensures \\result <==> (\\forall Integer i; this.has(i) <==> ((BSet) other).has(i));\n" + 
						"     */\n" + 
						"	public /*@ pure */ boolean equals(Object other) {\n" + 
						"		return other instanceof INT;\n" + 
						"	}\n" + 
						"	\n" + 
						"	/*@ also \n" + 
						"	 	requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result <==> false;\n" + 
						"     */\n" + 
						"    public /*@ pure */ boolean isEmpty() {\n" + 
						"    	return false;\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ int int_size() {\n" + 
						"        throw new UnsupportedOperationException(\"Error: size of the integers not representable\");\n" + 
						"    }  \n" + 
						"    \n" + 
						"    /*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result == \"INT\".hashCode();\n" + 
						"     */\n" + 
						"    public /*@ pure */ int hashCode() {\n" + 
						"    	return \"INT\".hashCode();\n" + 
						"    }\n" + 
						"    \n" + 
						"    /* inherited specifications should be correct for all set operations */\n" + 
						"    \n" + 
						"    public boolean isSubset(/*@ non_null @*/ TreeSet<Integer> s2) {\n" + 
						"    	return s2 instanceof INT;\n" + 
						"    }\n" + 
						"    \n" + 
						"    public boolean isProperSubset(/*@ non_null @*/ TreeSet<Integer> s2) {\n" + 
						"    	return false;\n" + 
						"    }\n" + 
						"    \n" + 
						"    public  boolean isSuperset(/*@ non_null @*/ TreeSet<Integer> s2) {\n" + 
						"    	return true;\n" + 
						"    }\n" + 
						"    \n" + 
						"    public boolean isProperSuperset(/*@ non_null @*/ TreeSet<Integer> s2) {\n" + 
						"    	return !(s2 instanceof INT);\n" + 
						"    }\n" + 
						"    \n" + 
						"    public Integer choose() {\n" + 
						"    	return rand.nextInt();\n" + 
						"    }\n" + 
						"    \n" + 
						"    public Object clone() {\n" + 
						"    	return this;\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"     	requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ BSet<Integer> insert(Integer i) {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't insert into the integers\");\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ BSet<Integer> remove(Integer i) {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't remove from the integers\");\n" + 
						"    }\n" + 
						"    \n" + 
						"    public BSet<Integer> intersection(TreeSet<Integer> s2) {\n" + 
						"    	if (s2 instanceof BSet) {\n" + 
						"    		return (BSet<Integer>) s2;\n" + 
						"    	} else {\n" + 
						"    		return new BSet<Integer>(s2);\n" + 
						"    	}\n" + 
						"    }\n" + 
						"	 \n" + 
						"    public BSet<Integer> union(TreeSet<Integer> s2) {\n" + 
						"    	return this;\n" + 
						"    }\n" + 
						"    \n" + 
						"    public BSet<Integer> difference(TreeSet<Integer> s2) {\n" + 
						"    	if (s2 instanceof INT) {\n" + 
						"    		return new BSet<Integer>();\n" + 
						"    	} else {\n" + 
						"    		throw new UnsupportedOperationException(\"Error: difference from the integers is infinite.\");\n" + 
						"    	}\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result.equals(\"INT\");\n" + 
						"     */\n" + 
						"    public /*@ pure */ String toString() {\n" + 
						"    	return \"INT\";\n" + 
						"    }\n" + 
						"    \n" + 
						"	public Iterator<Integer> toBag() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: a bag cannot contain the integers.\");		\n" + 
						"	}\n" + 
						"    \n" + 
						"    public ArrayList<Integer> toSequence() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: a sequence cannot contain the integers.\");		\n" + 
						"	}\n" + 
						"	\n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"	public /*@ pure */ Object [] toArray() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: an array cannot contain the integers.\");		\n" + 
						"	}\n" + 
						"	\n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"	public /*@ pure */ Iterator<Integer> iterator() {\n" + 
						"	   	throw new UnsupportedOperationException(\"Error: the integers are not iterable.\");		\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result <==> false;\n" + 
						"	 */\n" + 
						"    public /*@ pure */ boolean finite() {\n" + 
						"    	return false;\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ BSet<BSet<Integer>> pow() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't compute POW(INT).\");    	\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public BSet<BSet<Integer>> pow1() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't compute POW1(INT).\");    	\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> parts.length == 1 && parts[0] instanceof INT;\n" + 
						"     */\n" + 
						"    public /*@ pure */ boolean INT_partition(BSet<Integer> ... parts) {\n" + 
						"    	return parts.length == 1 && parts[0] instanceof INT;\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ Integer max() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't compute max of INT.\");    	    	\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ Integer min() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't compute min of INT.\");    	    	\n" + 
						"    }\n" + 
						"}";

		String NAT =
				"package eventb_prelude;\n" + 
						"\n" + 
						"\n" + 
						"/** representation of the EventB type NAT as a BSet\n" + 
						" * @author Tim Wahls & Nestor Catano & Victor Rivera\n" + 
						" */\n" + 
						"\n" + 
						"\n" + 
						"import java.util.ArrayList;\n" + 
						"import java.util.Iterator;\n" + 
						"\n" + 
						"\n" + 
						"public class NAT extends BSet<Integer> {\n" + 
						"	private NAT() {}\n" + 
						"	\n" + 
						"	public static final NAT instance = new NAT();\n" + 
						"	\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result <==> obj instanceof Integer && ((Integer) obj) >= 0;\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean has(Object obj) {\n" + 
						"		return INT.instance.has(obj) && ((Integer) obj) >= 0;\n" + 
						"	}\n" + 
						"	\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result <==> (\\forall Integer i; c.contains(i); this.has(i));\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean containsAll(java.util.Collection<?> c) {\n" + 
						"		for (Object i : c) {\n" + 
						"			if (i instanceof Integer) {\n" + 
						"				if ((Integer)i < 0) return false;\n" + 
						"			} else return false;\n" + 
						"		}\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"	\n" + 
						"	\n" + 
						"	/*@ also requires true; \n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result <==> obj instanceof BSet && (\\forall Integer i; this.has(i) <==> ((BSet) obj).has(i));\n" + 
						"	 */\n" + 
						"	public /*@ pure */ boolean equals(Object obj) {\n" + 
						"		return obj instanceof NAT;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result <==> false;\n" + 
						"	 */\n" + 
						"    public /*@ pure */ boolean isEmpty() {\n" + 
						"    	return false;\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ int int_size() {\n" + 
						"        throw new UnsupportedOperationException(\"Error: size of the NATs not representable\");\n" + 
						"    }  \n" + 
						"    \n" + 
						"    /* also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"       ensures \\result.equals(\"NAT\".hashCode());\n" + 
						"     */\n" + 
						"    public /*@ pure */ int hashCode() {\n" + 
						"    	return \"NAT\".hashCode();\n" + 
						"    }\n" + 
						"    \n" + 
						"    /** inherited specification should be correct for all set operations */\n" + 
						"    \n" + 
						"    public boolean isSubset(/*@ non_null @*/ BSet<Integer> s2) {\n" + 
						"    	return s2 instanceof INT || s2 instanceof NAT;\n" + 
						"    }\n" + 
						"    \n" + 
						"    public boolean isProperSubset(/*@ non_null @*/ BSet<Integer> s2) {\n" + 
						"    	return s2 instanceof INT;\n" + 
						"    }\n" + 
						"       \n" + 
						"    public  boolean isSuperset(/*@ non_null @*/ BSet<Integer> s2) {\n" + 
						"    	if (s2 instanceof INT) {\n" + 
						"    		return false;\n" + 
						"    	} else if (s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"    		return true;\n" + 
						"    	} else  {\n" + 
						"    		for (Integer i : s2) {\n" + 
						"    			if (i < 0) return false;\n" + 
						"    		}\n" + 
						"    		return true;\n" + 
						"    	}\n" + 
						"    }\n" + 
						"    \n" + 
						"    public boolean isProperSuperset(/*@ non_null @*/ BSet<Integer> s2) {\n" + 
						"    	if (s2 instanceof INT || s2 instanceof NAT) {\n" + 
						"    		return false;\n" + 
						"    	} else if (s2 instanceof NAT1) {\n" + 
						"    		return true;\n" + 
						"    	} else {\n" + 
						"    		for (Integer i : s2) {\n" + 
						"    			if (i < 0) return false;\n" + 
						"    		}\n" + 
						"    		return true;   		\n" + 
						"    	}\n" + 
						"    }\n" + 
						"\n" + 
						"    public Integer choose() {\n" + 
						"    	return 0;\n" + 
						"    }\n" + 
						"    \n" + 
						"    public Object clone() {\n" + 
						"    	return this;\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ BSet<Integer> insert(Integer i) {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't insert into the NATs\");\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ BSet<Integer> remove(Integer i) {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't remove from the NATs\");\n" + 
						"    }\n" + 
						"    \n" + 
						"    public BSet<Integer> intersection(BSet<Integer> s2) {\n" + 
						"    	if (s2 instanceof INT || s2 instanceof NAT) {\n" + 
						"    		return this;\n" + 
						"    	} else if (s2 instanceof NAT1) {\n" + 
						"    		return (NAT1) s2;\n" + 
						"    	} else {\n" + 
						"    		BSet<Integer> res = new BSet<Integer>();\n" + 
						"    		for (Integer i : s2) {\n" + 
						"    			if (i >= 0) {\n" + 
						"    				res = res.insert(i);\n" + 
						"    			}\n" + 
						"    		}\n" + 
						"    		return res;\n" + 
						"    	}\n" + 
						"     }\n" + 
						"	 \n" + 
						"    public BSet<Integer> union(BSet<Integer> s2) {\n" + 
						"    	if (s2 instanceof INT) {\n" + 
						"    		return INT.instance;\n" + 
						"    	} else if (s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"    		return this;\n" + 
						"    	} else {\n" + 
						"    		for (Integer i : s2) {\n" + 
						"    			if (i < 0) {\n" + 
						"    				throw new UnsupportedOperationException(\"Error: can't union with the NATs\");\n" + 
						"    			}\n" + 
						"    		}\n" + 
						"        	return this;\n" + 
						"    	}\n" + 
						"    }\n" + 
						"    \n" + 
						"    public BSet<Integer> difference(BSet<Integer> s2) {\n" + 
						"    	if (s2 instanceof INT || s2 instanceof NAT) {\n" + 
						"    		return new BSet<Integer>();\n" + 
						"    	} else if (s2 instanceof NAT1) {\n" + 
						"    		return new BSet<Integer>(0);   		\n" + 
						"    	} else {\n" + 
						"    		throw new UnsupportedOperationException(\"Error: difference from the integers is infinite.\");\n" + 
						"    	}\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result.equals(\"NAT\".toString());\n" + 
						"     */\n" + 
						"    public /*@ pure */ String toString() {\n" + 
						"    	return \"NAT\";\n" + 
						"    }\n" + 
						"    \n" + 
						"    public Iterator<Integer> toBag() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: a bag cannot contain the NATs.\");		\n" + 
						"	}\n" + 
						"    \n" + 
						"    public ArrayList<Integer> toSequence() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: a sequence cannot contain the NATs.\");		\n" + 
						"	}\n" + 
						"	\n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"         requires true;\n" + 
						"         assignable \\nothing;\n" + 
						"         signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"	public /*@ pure */ Object [] toArray() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: an array cannot contain the NATs.\");		\n" + 
						"	}\n" + 
						"	\n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"	public /*@ pure */ Iterator<Integer> iterator() {\n" + 
						"	   	throw new UnsupportedOperationException(\"Error: the NATs are not iterable.\");		\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result <==> false;\n" + 
						"	 */\n" + 
						"    public /*@ pure */ boolean finite() {\n" + 
						"    	return false;\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"    requires true;\n" + 
						"    assignable \\nothing;\n" + 
						"    signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ BSet<BSet<Integer>> pow() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't compute POW(NAT).\");    	\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"    requires true;\n" + 
						"    assignable \\nothing;\n" + 
						"    signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ BSet<BSet<Integer>> pow1() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't compute POW1(NAT).\");    	\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also requires parts.length == 1;\n" + 
						"          assignable \\nothing;\n" + 
						"          ensures \\result <==> parts[0] instanceof NAT;\n" + 
						"        also requires parts.length == 2;\n" + 
						"          assignable \\nothing;\n" + 
						"          ensures \\result <==> (parts[0] instanceof NAT1 && parts[1].equals(new BSet<Integer>(0))) ||\n" + 
						"            (parts[1] instanceof NAT1 && parts[0].equals(new BSet<Integer>(0)));\n" + 
						"        also requires parts.length == 0 || parts.length > 2;\n" + 
						"          assignable \\nothing;\n" + 
						"          ensures \\result <==> false;\n" + 
						"     */\n" + 
						"    public /*@ pure */ boolean NAT_partition(BSet<Integer> ... parts) {\n" + 
						"    	return (parts.length == 1 && parts[0] instanceof NAT) ||\n" + 
						"    	       (parts.length == 2 && parts[0] instanceof NAT1 && parts[1].equals(BSet.singleton(0))) ||\n" + 
						"    	       (parts.length == 2 && parts[1] instanceof NAT1 && parts[0].equals(BSet.singleton(0)));  	       \n" + 
						"    }\n" + 
						"    \n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ Integer max() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't compute max of NAT.\");    	    	\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result == 0;\n" + 
						"     */\n" + 
						"    public /*@ pure */ Integer min() {\n" + 
						"    	return 0;\n" + 
						"    }\n" + 
						"\n" + 
						"}";

		String NAT1 =
				"package eventb_prelude;\n" + 
						"\n" + 
						"\n" + 
						"/** representation of the EventB type NAT1 as a BSet\n" + 
						" * @author Tim Wahls & Nestor Catano & Victor Rivera\n" + 
						" */\n" + 
						"\n" + 
						"\n" + 
						"import java.util.ArrayList;\n" + 
						"import java.util.Iterator;\n" + 
						"\n" + 
						"\n" + 
						"public class NAT1 extends BSet<Integer> {\n" + 
						"	public static final NAT1 instance = new NAT1();\n" + 
						"	\n" + 
						"	private NAT1() {}\n" + 
						"	\n" + 
						"	\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result <==> obj instanceof Integer && ((Integer) obj) > 0;\n" + 
						"     */\n" + 
						"	public /*@ pure */ boolean has(Object obj) {\n" + 
						"		return INT.instance.has(obj) && ((Integer) obj) > 0;\n" + 
						"	}\n" + 
						"	\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result <==> (\\forall Integer i; c.contains(i); this.has(i));\n" + 
						"     */\n" + 
						"	public /*@ pure */ boolean containsAll(java.util.Collection<?> c) {\n" + 
						"		for (Object i : c) {\n" + 
						"			if (i instanceof Integer) {\n" + 
						"				if ((Integer)i <= 0) return false;\n" + 
						"			} else return false;\n" + 
						"		}\n" + 
						"		return true;\n" + 
						"	}\n" + 
						"	\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result <==> obj instanceof BSet && (\\forall Integer i; this.has(i) <==> ((BSet) obj).has(i));\n" + 
						"     */\n" + 
						"	public /*@ pure */ boolean equals(Object obj) {\n" + 
						"		return obj instanceof NAT1;\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"        ensures \\result <==> false;\n" + 
						"    */\n" + 
						"    public /*@ pure */ boolean isEmpty() {\n" + 
						"    	return false;\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ int int_size() {\n" + 
						"        throw new UnsupportedOperationException(\"Error: size of the NATs not representable\");\n" + 
						"    }  \n" + 
						"    \n" + 
						"    /*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result == \"NAT1\".hashCode();\n" + 
						"     */\n" + 
						"    public /*@ pure */ int hashCode() {\n" + 
						"    	return \"NAT1\".hashCode();\n" + 
						"    }\n" + 
						"    \n" + 
						"    /** inherited specification should be correct for all set operations */\n" + 
						"    \n" + 
						"    public boolean isSubset(/*@ non_null @*/ BSet<Integer> s2) {\n" + 
						"    	return s2 instanceof INT || s2 instanceof NAT || s2 instanceof NAT1;\n" + 
						"    }\n" + 
						"    \n" + 
						"    public boolean isProperSubset(/*@ non_null @*/ BSet<Integer> s2) {\n" + 
						"    	return s2 instanceof INT || s2 instanceof NAT;\n" + 
						"    }\n" + 
						"    \n" + 
						"    public  boolean isSuperset(/*@ non_null @*/ BSet<Integer> s2) {\n" + 
						"    	if (s2 instanceof INT || s2 instanceof NAT) {\n" + 
						"    		return false;\n" + 
						"    	} else if (s2 instanceof NAT1) {\n" + 
						"    		return true;\n" + 
						"    	} else  {\n" + 
						"    		for (Integer i : s2) {\n" + 
						"    			if (i <= 0) return false;\n" + 
						"    		}\n" + 
						"    		return true;\n" + 
						"    	}\n" + 
						"    }\n" + 
						"\n" + 
						"    public boolean isProperSuperset(/*@ non_null @*/ BSet<Integer> s2) {\n" + 
						"    	if (s2 instanceof INT || s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"    		return false;\n" + 
						"    	} else {\n" + 
						"    		for (Integer i : s2) {\n" + 
						"    			if (i <= 0) return false;\n" + 
						"    		}\n" + 
						"    		return true;   		\n" + 
						"    	}\n" + 
						"    }\n" + 
						"\n" + 
						"    public Integer choose() {\n" + 
						"    	return 0;\n" + 
						"    }\n" + 
						"\n" + 
						"    public Object clone() {\n" + 
						"    	return this;\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ BSet<Integer> insert(Integer i) {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't insert into the NAT1s\");\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ BSet<Integer> remove(Integer i) {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't remove from the NAT1s\");\n" + 
						"    }\n" + 
						"    \n" + 
						"    public BSet<Integer> intersection(BSet<Integer> s2) {\n" + 
						"    	if (s2 instanceof INT || s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"    		return this;\n" + 
						"    	} else {\n" + 
						"    		BSet<Integer> res = new BSet<Integer>();\n" + 
						"    		for (Integer i : s2) {\n" + 
						"    			if (i > 0) {\n" + 
						"    				res = res.insert(i);\n" + 
						"    			}\n" + 
						"    		}\n" + 
						"    		return res;\n" + 
						"    	}\n" + 
						"     }\n" + 
						"	 \n" + 
						"    public BSet<Integer> union(BSet<Integer> s2) {\n" + 
						"    	if (s2 instanceof INT || s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"    		return (BSet<Integer>) s2;\n" + 
						"    	} else {\n" + 
						"    		for (Integer i : s2) {\n" + 
						"    			if (i <= 0) {\n" + 
						"    				throw new UnsupportedOperationException(\"Error: can't union with the NATs\");\n" + 
						"    			}\n" + 
						"    		}\n" + 
						"        	return this;\n" + 
						"    	}\n" + 
						"    }\n" + 
						"\n" + 
						"    \n" + 
						"    public BSet<Integer> difference(BSet<Integer> s2) {\n" + 
						"    	if (s2 instanceof INT || s2 instanceof NAT || s2 instanceof NAT1) {\n" + 
						"    		return new BSet<Integer>();\n" + 
						"    	} else {\n" + 
						"    		throw new UnsupportedOperationException(\"Error: difference from the integers is infinite.\");\n" + 
						"    	}\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result.equals(\"NAT1\");\n" + 
						"     */\n" + 
						"    public /*@ pure */ String toString() {\n" + 
						"    	return \"NAT1\";\n" + 
						"    }\n" + 
						"\n" + 
						"    \n" + 
						"    public Iterator<Integer> toBag() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: a bag cannot contain the NAT1s.\");		\n" + 
						"	}\n" + 
						"    \n" + 
						"    public ArrayList<Integer> toSequence() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: a sequence cannot contain the NAT1s.\");		\n" + 
						"	}\n" + 
						"	\n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"	public /*@ pure */ Object [] toArray() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: an array cannot contain the NAT1s.\");		\n" + 
						"	}\n" + 
						"	\n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"	public /*@ pure */ Iterator<Integer> iterator() {\n" + 
						"	   	throw new UnsupportedOperationException(\"Error: the NAT1s are not iterable.\");		\n" + 
						"	}\n" + 
						"\n" + 
						"	/*@ also requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	    ensures \\result <==> false;\n" + 
						"	 */\n" + 
						"    public /*@ pure */ boolean finite() {\n" + 
						"    	return false;\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ BSet<BSet<Integer>> pow() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't compute POW(NAT1).\");    	\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"	requires true;\n" + 
						"	assignable \\nothing;\n" + 
						"	signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ BSet<BSet<Integer>> pow1() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't compute POW1(NAT1).\");    	\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"        ensures \\result <==> parts.length == 1 && parts[0] instanceof NAT1;\n" + 
						"     */\n" + 
						"    public /*@ pure */ boolean NAT1_partition(BSet<Integer> ... parts) {\n" + 
						"    	return (parts.length == 1 && parts[0] instanceof NAT1);\n" + 
						"    }\n" + 
						"    \n" + 
						"    /*@ also public exceptional_behavior\n" + 
						"        requires true;\n" + 
						"        assignable \\nothing;\n" + 
						"        signals (UnsupportedOperationException);\n" + 
						"     */\n" + 
						"    public /*@ pure */ Integer max() {\n" + 
						"    	throw new UnsupportedOperationException(\"Error: can't compute max of NAT1.\");    	    	\n" + 
						"    }\n" + 
						"    \n" + 
						"    /* also requires true;\n" + 
						"     	assignable \\nothing;\n" + 
						"       ensures \\result == 1;\n" + 
						"     */\n" + 
						"    public /*@ pure */ Integer min() {\n" + 
						"    	return 1;    	    	\n" + 
						"    }\n" + 
						"}";

		String Pair =
				"package eventb_prelude;\n" + 
						"\n" + 
						"\n" + 
						"/** representation of a pair of elements in Java\n" + 
						" * @author Tim Wahls & Nestor Catano & Victor Rivera\n" + 
						" */\n" + 
						"import java.io.Serializable;\n"+
						"\n" + 
						"\n" + 
						"public class Pair<K,V> implements Comparable<Pair<K,V>>, Serializable {\n" + 
						"	/*@ spec_public */ private final K fst;\n" + 
						"	/*@ spec_public */ private final V snd;\n" + 
						"	\n" + 
						"	/*@ spec_public */ private final boolean fstComparable;\n" + 
						"	/*@ spec_public */ private final boolean sndComparable;\n" + 
						"	\n" + 
						"	\n" + 
						"	public Pair(K k, V v) {\n" + 
						"		fst = k;\n" + 
						"		snd = v;\n" + 
						"		fstComparable = (k instanceof Comparable);\n" + 
						"		sndComparable = (v instanceof Comparable);\n" + 
						"	}\n" + 
						"\n" + 
						"	\n" + 
						"	/*@ requires true;\n" + 
						"	 	assignable \\nothing;\n" + 
						"	 	ensures \\result == snd;\n" + 
						"	*/	\n" + 
						"	public /*@ pure */ V snd() {\n" + 
						"		return snd;\n" + 
						"	}\n" + 
						"	\n" + 
						"	/*@ requires true;\n" + 
						" 		assignable \\nothing;\n" + 
						" 		ensures \\result == fst;\n" + 
						"	 */	\n" + 
						"	public /*@ pure */ K fst() {\n" + 
						"		return fst;\n" + 
						"	}\n" + 
						"	\n" + 
						"	public int compareTo(Pair<K,V> pair) {\n" + 
						"		if(fstComparable) {\n" + 
						"			int i = ((Comparable<K>) fst).compareTo(pair.fst);\n" + 
						"			if (i > 0) return 1;\n" + 
						"			if (i < 0) return -1;\n" + 
						"		}\n" + 
						"		\n" + 
						"		if(sndComparable) {\n" + 
						"			int i = ((Comparable<V>) snd).compareTo(pair.snd);\n" + 
						"			if (i > 0) return 1;\n" + 
						"			if (i < 0) return -1;\n" + 
						"		}\n" + 
						"		\n" + 
						"		return 0;\n" + 
						"	}	\n" + 
						"	\n" + 
						"	/*@ requires obj != null && (obj instanceof Pair);\n" + 
						" 		assignable \\nothing;\n" + 
						"    	ensures fst().equals(((Pair<K,V>) obj).fst()) && snd().equals(((Pair<K,V>) obj).snd);\n" + 
						"    	also\n" + 
						"    	requires !(obj != null && (obj instanceof Pair));\n" + 
						" 		assignable \\nothing;\n" + 
						"    	ensures false;\n" + 
						" */\n" + 
						"	public /*@ pure */ boolean equals(Object obj) {\n" + 
						"		if (obj != null && (obj instanceof Pair)) {\n" + 
						"			Pair<K,V> pair = (Pair<K,V>) obj;\n" + 
						"			return fst.equals(pair.fst) && snd.equals(pair.snd);\n" + 
						"		}\n" + 
						"		return false;\n" + 
						"	}\n" + 
						"	\n" + 
						"	public String toString() {\n" + 
						"		return \"(\"+fst+\",\"+snd+\")\";\n" + 
						"	}\n" + 
						"\n" + 
						"}";

		FileWriter fstream_bool = new FileWriter(path + File.separator+ "BOOL.java");
		BufferedWriter out_bool = new BufferedWriter(fstream_bool);
		out_bool.write(BOOL);
		out_bool.close();
		fstream_bool.close();
		FileWriter fstream_BRelation = new FileWriter(path + File.separator+ "BRelation.java");
		BufferedWriter out_BRelation = new BufferedWriter(fstream_BRelation);
		out_BRelation.write(BRelation);
		out_BRelation.close();
		fstream_BRelation.close();
		FileWriter fstream_BSet = new FileWriter(path + File.separator+ "BSet.java");
		BufferedWriter out_BSet = new BufferedWriter(fstream_BSet);
		out_BSet.write(BSet);
		out_BSet.close();
		fstream_BSet.close();
		FileWriter fstream_Enumerated = new FileWriter(path + File.separator+ "Enumerated.java");
		BufferedWriter out_Enumerated = new BufferedWriter(fstream_Enumerated);
		out_Enumerated.write(Enumerated);
		out_Enumerated.close();
		fstream_Enumerated.close();
		FileWriter fstream_ID = new FileWriter(path + File.separator+ "ID.java");
		BufferedWriter out_ID = new BufferedWriter(fstream_ID);
		out_ID.write(ID);
		out_ID.close();
		fstream_ID.close();
		FileWriter fstream_INT = new FileWriter(path + File.separator+ "INT.java");
		BufferedWriter out_INT = new BufferedWriter(fstream_INT);
		out_INT.write(INT);
		out_INT.close();
		fstream_INT.close();
		FileWriter fstream_NAT = new FileWriter(path + File.separator+ "NAT.java");
		BufferedWriter out_NAT = new BufferedWriter(fstream_NAT);
		out_NAT.write(NAT);
		out_NAT.close();
		fstream_NAT.close();
		FileWriter fstream_NAT1 = new FileWriter(path + File.separator+ "NAT1.java");
		BufferedWriter out_NAT1 = new BufferedWriter(fstream_NAT1);
		out_NAT1.write(NAT1);
		out_NAT1.close();
		fstream_NAT1.close();
		FileWriter fstream_Pair = new FileWriter(path + File.separator+ "Pair.java");
		BufferedWriter out_Pair = new BufferedWriter(fstream_Pair);
		out_Pair.write(Pair);
		out_Pair.close();
		fstream_Pair.close();
	}


}