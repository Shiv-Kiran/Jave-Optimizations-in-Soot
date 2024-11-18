import java.util.Iterator;
import java.util.List;
import java.util.*;

import soot.*;
import soot.Body;
import soot.NormalUnitPrinter;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.UnitPrinter;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.jimple.internal.*;

public class PA2 {
    public static void main(String[] args) {
        String classPath = "."; 	// change to appropriate path to the test class
        String dir = "./testcase"; 

        //Set up arguments for Soot
        String[] sootArgs = {
            "-cp", classPath, "-pp", // sets the class path for Soot
            "-keep-line-number", // preserves line numbers in input Java files  
            "-main-class", "Test",	// specify the main class
            // "Test", "Node",                   // list the classes to analyze
            "-process-dir", dir, 
            
            // "-p", "jb", "use-original-names:true",
            // send arguments to save jimple file 
            // "-f", "jimple", "-d", "output"
            

        };

        // Create transformer for analysis
        AnalysisTransformer analysisTransformer = new AnalysisTransformer();

        // Add transformer to appropriate pack in PackManager; PackManager will run all packs when soot.Main.main is called
        PackManager.v().getPack("jtp").add(new Transform("jtp.dfa", analysisTransformer));

        // Call Soot's main method with arguments
        soot.Main.main(sootArgs);

        // Print methodEscape Static Object from AnalysisTransformer 
        // System.out.println("Outside Everything : ");
        // Sort the methodEscape Map keys 
        List<String> sortedKeys = new ArrayList<>(analysisTransformer.methodEscape.keySet());
        Collections.sort(sortedKeys);

        for (String fullMethodName : sortedKeys) {
            List<String> escapeVals = analysisTransformer.methodEscape.get(fullMethodName);
            String[] split = fullMethodName.split(":");
            String className = split[0];
            String methodName = split[1];

            // Ignore if escapeVals is empty
            if (escapeVals.isEmpty()) {
                continue;
            }
            
            System.out.print(className + ":" + methodName + " ");
            for (String escapeVal : escapeVals) {
                System.out.print(escapeVal + " ");
            }
            System.out.println();
        }


        // for (Map.Entry<String, List<String>> entry : analysisTransformer.methodEscape.entrySet()) {
        //    String fullMethodName = entry.getKey();

        //     // Split into class name and method name class:method 
        //     String[] split = fullMethodName.split(":");
        //     String methodName = split[0];
        //     String className = split[1];


        //     List<String> escapeVals = entry.getValue();
        //     // Ignore if escapeVals is empty
        //     if (escapeVals.isEmpty()) {
        //         continue;
        //     }
            
        //     System.out.print(className + ":" + methodName + " ");
        //     for (String escapeVal : escapeVals) {
        //         // remove O from escapeVal String 
        //         // escapeVal = escapeVal.replace("O", "");
        //         System.out.print(escapeVal + " ");
        //     }
        //     System.out.println();
        // }

        
    }
}
