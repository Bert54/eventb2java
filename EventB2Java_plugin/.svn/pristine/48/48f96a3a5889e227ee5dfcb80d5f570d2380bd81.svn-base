package eventb2javajml_plugin.constraintsolver;

import java.util.List;
import java.util.Map;

public interface ConstraintSolver {
	
	/**
	 * Loads EventB machine
	 * @param resourcePath - path to EventB machine  
	 * @throws Exception
	 */
	void load(String resourcePath) throws Exception;

	/**
	 * Generates random values for constants 
	 * that reflect axioms and theorems
	 * @throws Exception
	 */
	Map generateValuesForConstants() throws Exception;	
	
	/**
	 * Returns generated Integer value for specified constant
	 * @param constName - name of constants, for which getting value
	 * @throws Exception
	 */
	Integer getGeneratedIntegerValue(String constName) throws Exception;
	
	/**
	 * Returns generated Boolean value for specified constant
	 * @param constName - name of constants, for which getting value
	 * @throws Exception
	 */
	Boolean getGeneratedBooleanValue(String constName) throws Exception;
	
	/**
	 * Returns generated values for BSet for specified constant
	 * @param constName - name of constants, for which getting value
	 * @throws Exception
	 */
	List getGeneratedBSet(String constName) throws Exception;
	
	/**
	 * Returns generated values for BRelation for specified constant
	 * @param constName - name of constants, for which getting value
	 * @throws Exception
	 */
	Map getGeneratedBRelation(String constName) throws Exception;

}
