package eventb2javajml_plugin.constraintsolver;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import com.google.inject.Guice;
import com.google.inject.Inject;
import com.google.inject.Injector;
import com.google.inject.Stage;

import de.prob.animator.domainobjects.AbstractEvalResult;
import de.prob.animator.domainobjects.EventB;
import de.prob.animator.domainobjects.IEvalElement;
import de.prob.scripting.Api;
import de.prob.statespace.State;
import de.prob.statespace.StateSpace;
import de.prob.statespace.Trace;

public class ProB implements ConstraintSolver {

	private Api api;
	private StateSpace stateSpace;
	private Map<IEvalElement, AbstractEvalResult> values;

	@Inject
	public ProB(Api api) {
		this.api = api;
	}
 
	 /**
	  * Loads EventB machine
	  * @param resourcePath - path to EventB machine  
	  * @throws Exception
	  */
	 public void load(String resourcePath) throws Exception {
		 // ProB configurations for Constraint Solver
		 Map<String, String> pref = new HashMap<String,String>();
		 pref.put("MAX_INITIALISATIONS", "100");
		 pref.put("MAXINT", "50");
		 pref.put("RANDOMISE_ENUMERATION_ORDER", "true");
		 pref.put("TIME_OUT", "10000");
		 
		 // Loading the Event-B machine
		 Path path = Paths.get(resourcePath);
		 this.stateSpace = api.eventb_load(path.toAbsolutePath().toString(), pref);
	 } 
 
	 /**
	  * Generates random values for constants 
	  * that reflect axioms and theorems
	  * @throws Exception
	  */
	 public Map generateValuesForConstants() throws Exception {
  		 Trace trace = new Trace(this.stateSpace); // Constructing trace    
		 trace = trace.anyEvent(null); // Initializing variables
  
		 State state = trace.getCurrentState();
		 this.values = state.getValues();  
		 
		 return this.values;
     }
	 
	 /**
	  * Returns generated Integer value for specified constant
	  * @param constName - name of constants, for which getting value
	  * @throws Exception
	  */
	 public Integer getGeneratedIntegerValue(String constName) throws Exception {
		 Set<IEvalElement> constants = null;
		 if (!values.isEmpty()) {
			 constants = values.keySet();
		 }
		 
		 for (IEvalElement constant : constants) {
			 if (constName.equals(constant.toString())) {
				 return Integer.parseInt(this.values.get(constant).toString());
			 }
		 } 
		 return null;
	 }
	 
	 /**
	  * Returns generated Boolean value for specified constant
	  * @param constName - name of constants, for which getting value
	  * @throws Exception
	  */
	 public Boolean getGeneratedBooleanValue(String constName) throws Exception {
		 Set<IEvalElement> constants = null;
		 if (!values.isEmpty()) {
			 constants = values.keySet();
		 }
		 
		 for (IEvalElement constant : constants) {
			 if (constName.equals(constant.toString())) {
				 return Boolean.parseBoolean(this.values.get(constant).toString());
			 }
		 } 
		 return null;
	 }	 
	 
	 /**
	  * Returns generated values for BSet for specified constant
	  * @param constName - name of constants, for which getting value
	  * @throws Exception
	  */
	 public List getGeneratedBSet(String constName) throws Exception {
		 List generatedValues = new ArrayList();
		 Set<IEvalElement> constants = null;
		 if (!values.isEmpty()) {
			 constants = values.keySet();
		 }
		 
		 for (IEvalElement constant : constants) {
			 if (constName.equals(constant.toString())) {
				 String[] valSet = this.values.get(constant).toString()
						 .replace("{", "").replace("}", "").replace("(", "").replace(")", "").replace("↦", ",")
						 .split(",");
				 
				 for (String v : valSet) {
					 generatedValues.add(v);
				 }
			 }
		 } 
		 return generatedValues;
	 }
	 
	 /**
	  * Returns generated values for BRelation for specified constant
	  * @param constName - name of constants, for which getting value
	  * @throws Exception
	  */
	 public Map getGeneratedBRelation(String constName) throws Exception {
		 Map generatedValues = new HashMap();
		 Set<IEvalElement> constants = null;
		 if (!values.isEmpty()) {
			 constants = values.keySet();
		 }
		 
		 for (IEvalElement constant : constants) {
			 if (constName.equals(constant.toString())) {
				 String[] valSet = this.values.get(constant).toString()
						 .replace("{", "").replace("}", "").replace("(", "").replace(")", "").replace("↦", ",")
						 .split(",");
				 
				 for (int i = 0; i < valSet.length - 1; i=i+2) {
					 generatedValues.put(valSet[i], valSet[i+1]);
				 }
			 }
		 } 
		 return generatedValues;
	 }
	 
}
