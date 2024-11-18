import java.util.*;
import soot.*;
import soot.jimple.AnyNewExpr;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JInvokeStmt;
import soot.jimple.ThisRef;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.BackwardFlowAnalysis;
import soot.toolkits.scalar.FlowSet;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.InvokeStmt;
import soot.jimple.NewExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.ParameterRef;
import soot.jimple.internal.JThrowStmt;
import soot.jimple.internal.JArrayRef;
import soot.jimple.internal.JNewArrayExpr;
import soot.jimple.Stmt;
import soot.jimple.VirtualInvokeExpr;
import soot.jimple.internal.JVirtualInvokeExpr;
import soot.jimple.internal.JInterfaceInvokeExpr;
import soot.jimple.internal.JCastExpr;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;

// import javafx.util.Pair;
import soot.util.*;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.io.IOException;
import soot.util.dot.DotGraph;
import soot.util.queue.QueueReader;
import soot.toolkits.scalar.SimpleLiveLocals;
import soot.toolkits.scalar.LiveLocals;



class State {
    public Map<String, Set<String>> stack;
    public Map<String, Set<String>> heap;

    public State() {
        this.stack = new HashMap<>();
        this.heap = new HashMap<>();
    }
    
	public void print() {
		printSection("Stack", stack);
		printSection("Heap", heap);
	}

	private void printSection(String title, Map<String, Set<String>> map) {
		System.out.println("------------ " + title + " ------------");
		for (Map.Entry<String, Set<String>> entry : map.entrySet()) {
			System.out.println(entry.getKey() + " : " + entry.getValue());
		}
	}

	public void union(State other) {
    other.stack.forEach((key, otherSet) ->
            stack.merge(key, otherSet, (existingSet, newSet) -> {
                existingSet.addAll(newSet);
                return existingSet;
            }));

    other.heap.forEach((key, otherSet) ->
            heap.merge(key, otherSet, (existingSet, newSet) -> {
                existingSet.addAll(newSet);
                return existingSet;
            }));
	}

	public boolean checkDiff(State other) {
		boolean stackDiff = this.stack.equals(other.stack);
		boolean heapDiff = this.heap.equals(other.heap);
		return stackDiff && heapDiff;
    }
    
	public void copy(State other) {
		this.stack.clear();
		this.stack.putAll(other.stack);

		this.heap.clear();
		this.heap.putAll(other.heap);
	} 
}
	
// -- Change it to SceneTransformer, CHA - Class Hiera
public class AnalysisTransformer extends SceneTransformer {

	// Map of method Name and set of escaping objects
	static Map<String, List<String>> methodEscape = new HashMap<>(); 
	
	// Set of all escaped Objects	
	static Set<String> escapeObjs =  new HashSet<>();

	//  <obj, lineNO> 
	static Map<String, String> garbageObjs = new HashMap<>();
	

	static Map<Unit,String>allocationSite = new HashMap<>();


	

	static CallGraph cg;


	protected static void processCFG(SootMethod method) {
        if(method.toString().contains("init")  ) { return; }
        Body body = method.getActiveBody();
        // Get the callgraph 
        UnitGraph cfg = new BriefUnitGraph(body);
        // Get live local using Soot's exiting analysis
        LiveLocals liveLocals = new SimpleLiveLocals(cfg);
        // Units for the body
        PatchingChain<Unit> units = body.getUnits();
        System.out.println("\n----- " + body.getMethod().getName() + "-----");
        for (Unit u : units) {
            System.out.println("Unit: " + u);
            List<Local> before = liveLocals.getLiveLocalsBefore(u);
            List<Local> after = liveLocals.getLiveLocalsAfter(u);
            System.out.println("Live locals before: " + before);
            System.out.println("Live locals after: " + after);
            System.out.println();


            // Iterator of getEdgesOutof method
            Iterator<Edge> edges = cg.edgesOutOf(u);
            while (edges.hasNext()) {
                Edge edge = edges.next();
                SootMethod targetMethod = edge.tgt();
                if (targetMethod.isJavaLibraryMethod()) {
                    continue;
                }
                System.out.println("Edge: " + edge);
                System.out.println("Target method: " + targetMethod);
                System.out.println();
            }

        }
    }
	
	
	public static void generateDotFile(UnitGraph graph, String fileName) {
        String directory = "./diagram/";

        // Create the directory if it doesn't exist
        File dir = new File(directory);
        if (!dir.exists()) {
            boolean created = dir.mkdirs();
            if (!created) {
                System.err.println("Error creating directory: " + directory);
                return;
            }
        }

        try {
            // save the graph to a .dot file in diagram directory 


            FileWriter fileWriter = new FileWriter(directory + fileName);
            PrintWriter printWriter = new PrintWriter(fileWriter);

            printWriter.println("digraph G {");
            for (Unit unit : graph) {
                printWriter.println("\t\"" + unit + "\";");
                for (Unit succ : graph.getSuccsOf(unit)) {
                    printWriter.println("\t\"" + unit + "\" -> \"" + succ + "\";");
                }
            }
            printWriter.println("}");

            printWriter.close();
            fileWriter.close();

            System.out.println("Graph generated successfully as " + fileName);
        } catch (IOException e) {
            System.err.println("Error generating graph: " + e.getMessage());
        }
    }


	// create dot file for callgraph of only non-init, java, and soot classes 
	public static void generateCallGraph(CallGraph graph, String fileName) { 
		if (fileName == null) { 
			fileName = soot.SourceLocator.v().getOutputDir(); 
			}
		//		if (fileName.length() > 0) { 
		//				fileName = fileName + File.separator; 
		//			} 
		 String directory = "./diagram/";
	 File dir = new File(directory);
        if (!dir.exists()) {
            boolean created = dir.mkdirs();
            if (!created) {
                System.err.println("Error creating directory: " + directory);
                return;
            }
        }
		fileName = directory + fileName + "-call-graph" + DotGraph.DOT_EXTENSION; 
		
		// System.out.println("writing to file " + fileName); 
		DotGraph canvas = new DotGraph("call-graph"); 
		QueueReader<Edge> listener = graph.listener(); 
		while (listener.hasNext()) { 
			Edge next = listener.next(); 
			MethodOrMethodContext src = next.getSrc(); 
			MethodOrMethodContext tgt = next.getTgt(); 
			String srcString = src.toString(); 
			String tgtString = tgt.toString(); 
			// remove init calls too 


			if ((!srcString.startsWith("<java.") && !srcString.startsWith("<sun.") 
					&& !srcString.startsWith("<org.") && !srcString.startsWith("<com.") 
					&& !srcString.startsWith("<jdk.") && !srcString.startsWith("<javax.") && !srcString.contains("<init>"))
					||
				(!tgtString.startsWith("<java.") && !tgtString.startsWith("<sun.")
					&& !tgtString.startsWith("<org.") && !tgtString.startsWith("<com.")
					&& !tgtString.startsWith("<jdk.") && !tgtString.startsWith("<javax.")  )) {


						if (srcString.contains("<init>") || tgtString.contains("<init>")) {
							continue;
						}
						canvas.drawNode(src.toString());
						canvas.drawNode(tgt.toString());
						canvas.drawEdge(src.toString(), tgt.toString());
						//System.out.println("src = " + srcString);
						System.out.println("tgt = " + tgtString);

						
					}
		}
		canvas.plot(fileName);
		return;
	}
	


	public void getUnitInfo(Unit u ){
        // Print its instance type and line number


        System.out.println("Code at line: " + u.getJavaSourceStartLineNumber() + " = " + u.toString());
        System.out.println("Unit: " + u.getClass() + " " + u.getJavaSourceStartLineNumber());

        if (u instanceof JAssignStmt) {
            JAssignStmt assignStmt = (JAssignStmt) u;
            Value left = assignStmt.getLeftOp();
            Value right = assignStmt.getRightOp();

            // print if they are local 
            if (left instanceof Local) {
                System.out.println("Local Left: " + left);
            }
            if (right instanceof Local) {
                System.out.println("Local Right: " + right);
            }

            // Print the left and right operands
            System.out.println("Left: " + left);
            System.out.println("Right: " + right);
        }
        if (u instanceof JInvokeStmt) {
			// Methods from unit u using cg.getEdgesOutOf(u)
			// print unit 
		



            JInvokeStmt invokeStmt = (JInvokeStmt) u;
            System.out.println("Invoke: " + invokeStmt);
            // Print its parameters and return value 
            System.out.println("Parameters: " + invokeStmt.getInvokeExpr().getArgs());
            System.out.println("Return value: " + invokeStmt.getInvokeExpr().getMethod().getReturnType());

            // In variable is the return value stored into 
            if (invokeStmt.getInvokeExpr().getMethod().getReturnType() != VoidType.v()) {
                System.out.println("In variable: ");
            }


        }
        // Print the unit's content
        System.out.println("Content: " + u);
    }
	
	public State evalUnit(Unit u , State inUnits) 
	{
		
		
		State out = new State(); 
		out.copy(inUnits);
		
		
		
		if(u instanceof DefinitionStmt) {
			
			DefinitionStmt st = (DefinitionStmt) u;
			Value rightStmt = st.getRightOp();
			Value leftStmt =st.getLeftOp();
			
			// line number 13 print details
			// if (u.getJavaSourceStartLineNumber() == 10) {
			// 	System.out.println("Line 50: " + u);
			// 	System.out.println("Class 13: " + u.getClass());
			// 	System.out.println("Left: " + leftStmt + " " + leftStmt.getClass());
			// 	System.out.println("Right: " + rightStmt + " " + rightStmt.getClass());
			// 	// print stack 
			// 	System.out.println("Stack: " + inUnits.stack);
			// } 
			
			
			
			if (leftStmt.getType() instanceof PrimType || rightStmt.getType() instanceof PrimType) {
		        return inUnits;
		    }

			//-----------X = new A()--------------
			if( leftStmt instanceof Local && rightStmt instanceof NewExpr) {
				
				if(!allocationSite.containsKey(u)) {
					String Obj = "O"+ u.getJavaSourceStartLineNumber();
					allocationSite.put(u, Obj);
					Set<String> values =new HashSet<>();
					values.add(Obj);
					// Print leftStmt 
					// System.out.println("New A() Line No : " + u.getJavaSourceStartLineNumber() + " Unit : " + u + " Class : " + rightStmt.getClass() + " Stack : " + out.stack + " left " + leftStmt);

					out.stack.put(leftStmt.toString(),values);

					// Print out stack 
					// System.out.println("Out Stack : " + out.stack + " " + out.heap); 
				}
				else {
					Set<String> values =new HashSet<>();
					values.add(allocationSite.get(u));
					out.stack.put(leftStmt.toString(),values);
				}
				
				NewExpr newExpr = (NewExpr) rightStmt;
				RefType refType = newExpr.getBaseType();
				SootClass sootClass = refType.getSootClass();
				Chain<SootField> fields =  sootClass.getFields();
				String obj =allocationSite.get(u); 

				// get fields of parent class if any Inheritance
				SootClass parent = sootClass.getSuperclass();
				if (parent != null) {
						Chain<SootField> parentFields = parent.getFields();
						for (SootField field : parentFields) {
							if(!field.isStatic()) {
								String ObjField = obj+"."+field.getName();
								Set<String> values =new HashSet<>();
								out.heap.put(ObjField, values);
							} 
						}
				}
				
								
				for (SootField field : fields) {	
					if(!field.isStatic()) {
						String ObjField = obj+"."+field.getName();
						Set<String> values =new HashSet<>();
						out.heap.put(ObjField, values);
					} 
				}

				// Print LineNumber, Unit, class 
				// System.out.println("New A() Line No : " + u.getJavaSourceStartLineNumber() + " Unit : " + u + " Class : " + sootClass + " Stack : " + out.stack);
				

			}
			
			// X = arr[] 
			if( leftStmt instanceof Local && rightStmt instanceof JNewArrayExpr) {
				
				
				//--------Make entry in stack according to allocationSite Map -----------


				
				if(!allocationSite.containsKey(u)) {
					
					String Obj = "O"+ u.getJavaSourceStartLineNumber();
					allocationSite.put(u, Obj);
					Set<String> values =new HashSet<>();
					values.add(Obj);
					out.stack.put(leftStmt.toString(),values);
						
				}
				else {
					
					Set<String> values =new HashSet<>();
					values.add(allocationSite.get(u));
					out.stack.put(leftStmt.toString(),values);
				}

				JNewArrayExpr newExpr = (JNewArrayExpr) rightStmt;
				Type refType = newExpr.getBaseType();
				Value size = newExpr.getSize();
				
				String obj =allocationSite.get(u); 
				
				// Initialize each field as X.1 and X.2 up X.size
				for (int i = 0; i < Integer.parseInt(size.toString()); i++) {
					Set<String> values =new HashSet<>();
					out.heap.put(obj+"."+i, values);
				}

				// Print LineNumber, Unit, class 
				// System.out.println("New Arr() Line No : " + u.getJavaSourceStartLineNumber() + " Unit : " + u + " Class : " + size.toString() + " Stack : " + out.stack);
				
			}

			//-----------X = Y----------------------
			
			else if( leftStmt instanceof Local && rightStmt instanceof Local ) {				
				Set<String> values = new HashSet<>();
				
				if(inUnits.stack.get(rightStmt.toString())!=null) {
					values.addAll(inUnits.stack.get(rightStmt.toString()));
				}
				
				out.stack.put(leftStmt.toString(), values);
				
				for(String val : values) {
					for(String field : inUnits.heap.keySet()) {
						if(field.contains(val)) {
							out.heap.put(field,inUnits.heap.get(field));
						}
					}
				}
			}
			
			//---------------X = Y.f--------------------
			
			else if(leftStmt instanceof Local && rightStmt instanceof FieldRef ) {
				
				if (rightStmt instanceof InstanceFieldRef) {
					InstanceFieldRef fieldRef = (InstanceFieldRef) rightStmt;
		    	    Value base = fieldRef.getBase();
		    	    SootField field = fieldRef.getField();
		    	    String Y_base = base.toString();
		    	    String fieldName = field.getName();
				    
				    Set<String> ref = new HashSet<>();
				    Set<String> yref = new HashSet<>();

				    if(inUnits.stack.get(Y_base)!=null) {
				    	yref.addAll(inUnits.stack.get(Y_base));
				    }

					// if Y is escaping then X is escaping too 
					// System.out.println("Load Y.f Line No : " + u.getJavaSourceStartLineNumber() + " X_base : " + Y_base + " FieldName : " + fieldName + " Unit : " + u + "Stack : " + inUnits.stack + "escapeObjs " + escapeObjs);


				    
				    
				    
				    for(String val : yref) {
						String valField = val+"."+fieldName;
				    	if (inUnits.heap.get(valField) != null)
					    	ref.addAll(inUnits.heap.get(valField));
						else if (val.equals("Oglob")){
							ref.add("Oglob");
							}	
						// else 
						// 	System.out.println("HeapError : " + val + "." + fieldName + " " + inUnits.heap);
				    }
				    
				    out.stack.put(leftStmt.toString(), ref);

					
				}
				
				// Escaping : X = Y.f where Y is static
				
				else if(rightStmt instanceof StaticFieldRef) {
					// System.out.println("Right is Static : " + u.toString() + " " + u.getJavaSourceStartLineNumber());
					Set<String> ref = new HashSet<>();
					ref.add("Oglob");
					out.stack.put(leftStmt.toString(), ref);
				    
				}
			}
			
			//----------------X.f = y--------------------
			
			else if( leftStmt instanceof FieldRef && rightStmt instanceof Local) {
				
				// Escaping : X.f = Y where X is static
				
				if(leftStmt instanceof StaticFieldRef) {
					if (inUnits.stack.containsKey(rightStmt.toString())) {
						// out.heap.put("Oglob."+leftStmt.toString(), inUnits.stack.get(rightStmt.toString()));
						escapeObjs.addAll(inUnits.stack.get(rightStmt.toString()));
					}

				}
				
				
				else {
					
					InstanceFieldRef fieldRef = (InstanceFieldRef) leftStmt;
		    	    Value base = fieldRef.getBase();
		    	    SootField field = fieldRef.getField();
		    	    String X_base = base.toString();
		    	    String fieldName = field.getName();

		    	    Set<String> value = inUnits.stack.get(rightStmt.toString());
		    	    
		    	    //get set of references from stack of X

					// Print line number, X_base, fieldname , unit 
					// System.out.println("X.f = Y Line No : " + u.getJavaSourceStartLineNumber() + " X_base : " + X_base + " FieldName : " + fieldName + " Unit : " + u + "Stack : " + inUnits.stack);
		    	    
		    	    
		    	    if (inUnits.stack.containsKey(X_base)) {

            	    	Set<String> refs = inUnits.stack.get(X_base);

		    	    if(refs.size()<=1) {
						
		    	    	for(String ref : refs ) {
							out.heap.put(ref+"."+fieldName, value);
		    	    		if(escapeObjs.contains(ref) || ref.contains("Oglob") ) {
		    	    			escapeObjs.addAll(value);
		    	    		}
		    	    	}
		    	    }
		    	    else {
		    	    	for(String ref : refs ) {	
		    	    		out.heap.get(ref+"."+fieldName).addAll( value);
		    	    		if(escapeObjs.contains(ref)) {
		    	    			escapeObjs.addAll(value);
		    	    		}
		    	    	}
		    	    }
            	    }
		    	    
				    
				}
				
			}

			// X = foo(a,b,c); Need to introduce Inter 
			else if (rightStmt instanceof VirtualInvokeExpr) {
				// make args of rightStmt to escape 
				// System.out.println("X = foo() Line No : " + u.getJavaSourceStartLineNumber() + " X_base : " + leftStmt + " Y_base : " + rightStmt + " Unit : " + u + "Stack : " + inUnits.stack);
				VirtualInvokeExpr invokeExpr = (VirtualInvokeExpr) rightStmt;
				List<Value> args = invokeExpr.getArgs();
				// for (Value arg : args) {
				// 	if (inUnits.stack.containsKey(arg.toString())) {
				// 		escapeObjs.addAll(inUnits.stack.get(arg.toString()));
				// 	}
				// }
				String method = invokeExpr.getMethod().getName();
				SootMethod m = invokeExpr.getMethod();
				Body b = m.getActiveBody();

				// if (! m.isConstructor()){
				// 	out = IntraEscapeAnalysis(b, inUnits);
				// 	// Print out 
				// 	System.out.println("Out : " + out.stack + " " + out.heap);
				// 	out.print(); 
				// }


				



			}

			else if (rightStmt instanceof ParameterRef){ 
				// Add to stack and escape as Oglob 
				Set<String> ref = new HashSet<>();
				ref.add("Oglob_" + leftStmt.toString());
				out.stack.put(leftStmt.toString(), ref);
				escapeObjs.addAll(ref);

			}

			// .this variable 
			else if (rightStmt instanceof ThisRef){
				// Add to stack and escape as Oglob 
				Set<String> ref = new HashSet<>();
				ref.add("Oglob_" + leftStmt.toString() );
				out.stack.put(leftStmt.toString(), ref);
				escapeObjs.addAll(ref);
			}

			// global casting X = Y but Y is this statement  
			else if (rightStmt instanceof JCastExpr){
				// Add to stack and escape as Oglob 
				// if Y is of Oglob stack then X is also of Oglob stack
				// ref of X is ref of Y
				JCastExpr castExpr = (JCastExpr) rightStmt;
				String Y_base = castExpr.getOp().toString(); 
				Set<String> ref = new HashSet<>();
				Set<String> yref = new HashSet<>();

				if(inUnits.stack.get(Y_base)!=null) {
					yref.addAll(inUnits.stack.get(Y_base));
				}

				// print line number, Y_base, unit, leftStmt 
				// System.out.println("X = Y Line No : " + u.getJavaSourceStartLineNumber() + " X_base : " + leftStmt + " Y_base : " + Y_base + " Unit : " + u + "Stack : " + inUnits.stack);

				for(String val : yref) {
					if (inUnits.heap.get(val) != null)
						ref.addAll(inUnits.heap.get(val));
					else if (val.equals("Oglob")){
						ref.add("Oglob");
						}	
					// else 
					// 	System.out.println("HeapError : " + val  + " " + inUnits.heap);
				}
				    
				out.stack.put(leftStmt.toString(), ref);
			}
			// Use Index as field X[0] = Y
			else if (leftStmt instanceof JArrayRef && rightStmt instanceof Local) {
				JArrayRef fieldRef = (JArrayRef) leftStmt;
		    	    Value base = fieldRef.getBase();
		    	    Value field = fieldRef.getIndex();
		    	    String X_base = base.toString();
		    	    String fieldName = field.toString();

		    	    Set<String> value = inUnits.stack.get(rightStmt.toString());
		    	    

					// Print line number, X_base, fieldname , unit 
					// System.out.println("X[0] = Y Line No : " + u.getJavaSourceStartLineNumber() + " X_base : " + X_base + " FieldName : " + fieldName + " Unit : " + u + "Stack : " + inUnits.stack);
		    	    
		    	    if (inUnits.stack.containsKey(X_base)) {

            	    	Set<String> refs = inUnits.stack.get(X_base);

		    	    if(refs.size()<=1) {
		    	    	for(String ref : refs ) {
		    	    		out.heap.put(ref+"."+fieldName, value);
		    	    		if(escapeObjs.contains(ref) || ref.contains("Oglob") ) {
		    	    			escapeObjs.addAll(value);
		    	    		}
		    	    	}
		    	    }
		    	    else {
		    	    	for(String ref : refs ) {
		    	    		
		    	    		out.heap.get(ref+"."+fieldName).addAll( value);
		    	    		if(escapeObjs.contains(ref)) {
		    	    			escapeObjs.addAll(value);
		    	    		}
		    	    	}
		    	    }
				}
			}

			// X = Y[0]
			else if (leftStmt instanceof Local && rightStmt instanceof JArrayRef) {
				JArrayRef fieldRef = (JArrayRef) rightStmt;
				Value base = fieldRef.getBase();
				Value field = fieldRef.getIndex();
				String Y_base = base.toString();
				String fieldName = field.toString();

				// Search for Y.f in heap and add to X 
				Set<String> ref = new HashSet<>();
				Set<String> yref = new HashSet<>();

				if(inUnits.stack.get(Y_base)!=null) {
					yref.addAll(inUnits.stack.get(Y_base));
				}

				for (String val : yref) {
					if (inUnits.heap.get(val+"."+fieldName) != null)
						ref.addAll(inUnits.heap.get(val+"."+fieldName));
					else if (val.equals("Oglob")){
						ref.add("Oglob");
						}	
					// else 
					// 	System.out.println("HeapErrorArr : " + val + "." + fieldName + " " + inUnits.heap);
				}
				    
				out.stack.put(leftStmt.toString(), ref);


					
			}

			// else {
			// 	System.out.println("AssignStmt: "+u.toString() + " Line No : " + u.getJavaSourceStartLineNumber() + u.getClass());
			// 	// Print Left and Right 
			// 	System.out.println("Left: "+leftStmt.toString() + " class : " + leftStmt.getClass());
			// 	System.out.println("Right: "+rightStmt.toString() + " class : " + rightStmt.getClass());

			// }
		
		}
			
		// foo(a,b,c)  or r.foo(a,b,c)
		else if(u instanceof InvokeStmt) {

			// if (u instanceof JInvokeStmt) {
			// 	// System.out.println("Unit JInvokeStmt: " + u + " Line No : " + u.getJavaSourceStartLineNumber() + " Class : " + u.getClass());
			// 	Iterator<Edge> edges = cg.edgesOutOf(u); 
			// 	while(edges.hasNext()) {
			// 		Edge edge = edges.next();
			// 		SootMethod targetMethod = edge.tgt();
			// 		if (targetMethod.isJavaLibraryMethod() || targetMethod.isConstructor()) {
			// 			continue;
			// 		}
			// 		State temp = new State();
			// 		temp.copy(out);

			// 		// temp = IntraEscapeAnalysis(targetMethod.getActiveBody(), temp);
			// 		// Print out
			// 		// System.out.println("Temp : " + temp.stack + " " + temp.heap);

			// 		out = temp ; 
					
			// 	}

			// }

			// Other than constructors 
			if(!u.toString().contains("init") ) {
				

				// Print if lineNumber = 18 
				// if (u.getJavaSourceStartLineNumber() == 50) {
				// 	System.out.println("Invoke 50: ");
					// System.out.println("Line 50: " + u);
					// System.out.println("Class 18: " + u.getClass());
				// }

				String method = u.toString();

				// Make args of method to escape 
				InvokeStmt stmt = (InvokeStmt) u;
				InvokeExpr expr = stmt.getInvokeExpr();
				List<Value> args = expr.getArgs();
				// print args 
				// System.out.println("InvokeArgs: " + args + " expr " + expr.toString() + " stmt " + stmt.toString() + " u " + u.toString() + " Line No : " + u.getJavaSourceStartLineNumber() + " Type : " + u.getClass() + "Stack : " + inUnits.stack );
				
				// If r.foo() is the call get r 
				Value base = null;
				if (expr instanceof VirtualInvokeExpr) {
					VirtualInvokeExpr virtualInvokeExpr = (VirtualInvokeExpr) expr;
					base = virtualInvokeExpr.getBase();
					if (inUnits.stack.containsKey(base.toString())) {
						// print if lineNumber = 18
						// System.out.println("Base: " + base.toString() + " Line No : " + u.getJavaSourceStartLineNumber() + " Type : " + u.getClass() + "Stack : " + inUnits.stack);
						escapeObjs.addAll(inUnits.stack.get(base.toString()));
					}

					// System.out.println("Base: " + base.toString() + " Line No : " + u.getJavaSourceStartLineNumber() + " Type : " + u.getClass() + "Stack : " + inUnits.stack);
					
					// for(SootMethod m : functState.keySet()){
					// 	if(m.getName().equals(method)) {
							
					// 		Value baseValue = virtualInvokeExpr.getBase();

					// 		if (baseValue instanceof Local) {
					// 			Local baseLocal = (Local) baseValue;
					// 			State newIn = new State(); 
					// 			newIn.stack.put("this", inUnits.stack.get(baseLocal.toString()));
					// 			Set<String> values = inUnits.stack.get(baseLocal.toString());

					// 			for (String val: values) {
					// 				for (String field: inUnits.heap.keySet()){
					// 					if(field.contains(val)) {
					// 						Set<String> ref = new HashSet<>(); 
					// 						ref.addAll(inUnits.heap.get(field));
					// 						newIn.heap.put(field, ref);
					// 					}
					// 				}
					// 			}

					// 			if(!newIn.equals(functState.get(m).getKey())) {
									
					// 				functState.get(m).getKey().union(newIn);

					// 				CHAqueue.push(m);
					// 				CHAworklist.add(m);
					// 			}
					// 			State funOut = new State(); 
					// 			funOut.copy(functState.get(m).getValue());	

					// 			if(funOut.stack.get("this") !=null) {
					// 				Set<String> value = new HashSet<>();
					// 				value.addAll(out.stack.get(baseLocal.toString()));
					// 				for (String val : value) {
					// 					for (String field : funOut.heap.keySet()) {
					// 						if (field.contains(val)) {
					// 							out.heap.put(field, funOut.heap.get(field));
					// 						}
					// 					}
					// 				}
					// 			}

								
					// 		}
					// 		break; 
					// 	}
					// }
				}

				for (Value arg : args) {
					if (inUnits.stack.containsKey(arg.toString())) {
						escapeObjs.addAll(inUnits.stack.get(arg.toString()));
					}
				}
			}
			
		}

		// return r;
		else if (u instanceof ReturnStmt) {
			// Escape all objects in the return statement 
			// System.out.println("Return: "+u.toString() + inUnits.stack);
			ReturnStmt stmt = (ReturnStmt) u;
			Value ret = stmt.getOp();
			if (inUnits.stack.containsKey(ret.toString())) {
			// System.out.println("Return: "+ret.toString() + inUnits.stack.get(ret.toString()));
				escapeObjs.addAll(inUnits.stack.get(ret.toString()));
			}
		}

		// throw r;
		else if (u instanceof JThrowStmt) {
			// Escape all objects in the throw statement 
			// System.out.println("Throw: "+u.toString());
			JThrowStmt stmt = (JThrowStmt) u;
			Value ret = stmt.getOp();
			if (inUnits.stack.containsKey(ret.toString())) {
				// System.out.println("Throw: "+ret.toString() + inUnits.stack.get(ret.toString()));
				escapeObjs.addAll(inUnits.stack.get(ret.toString()));
			}
		}

		// else {
			// System.out.println("Other "+u.toString() + " Line No : " + u.getJavaSourceStartLineNumber() + u.getClass());		
		// }

		// if Linenumber is between 37 and 39 print stack and heap 
		
		

		return out;
	}
	
	public State IntraEscapeAnalysis (Body B, State In) {
		
		// Create new Worklist
			    
	    UnitGraph g = new BriefUnitGraph(B);
		// generateDotFile(g, "cfg_" + B.getMethod().getName() + ".dot");

	    Map<Unit,State> inUnits = new HashMap<>();
	    
	    Set<Unit> Workset = new HashSet<>();
	    Queue<Unit> worklist = new LinkedList<>();
	    
	    for (Unit u : g.getBody().getUnits()) {
	        Workset.add(u);
	        worklist.offer(u);
	       State temp = new State();
	       inUnits.put(u, temp);
	    }
	    
	    
	    
	    
	    // -------- Fixed Point Algorithm --------
	    
		while (!worklist.isEmpty()) {
			State stateChange = new State();
			State NetChange = new State();
			NetChange.copy(In);
			
			Unit n = worklist.poll();
			Workset.remove(n);
			
			// Predecessors
			List<Unit> predecessors = g.getPredsOf(n);

			// NO Predecessors 
			if (predecessors.isEmpty()) {
				stateChange = evalUnit(n, new State());    
				NetChange.stack.putAll(stateChange.stack);
				NetChange.heap.putAll(stateChange.heap);
			}

			else if(predecessors.size()==1){
				for(Unit P : predecessors) {
					stateChange = evalUnit(n,inUnits.get(P));                  
					NetChange.stack.putAll(stateChange.stack);
					NetChange.heap.putAll(stateChange.heap);
				}
			}        
			else {
				for(Unit P : predecessors) {                 
					// if (P.getJavaSourceStartLineNumber() == 12) {
					//     // print lin number, type, and unit class
					//     System.out.println("Work No : " + n.getJavaSourceStartLineNumber() + " Type : " + n.getClass() + " Unit : " + n);
					// }
					stateChange = evalUnit(n,inUnits.get(P));
					NetChange=mergeChanges(stateChange,NetChange);
				}
			}
			
			// Successors
			if (!inUnits.get(n).checkDiff(NetChange)) {
				inUnits.put(n, NetChange);
				List<Unit> successors = g.getSuccsOf(n);
				for (Unit succ : successors) {
					if (!Workset.contains(succ)) {
						worklist.offer(succ);
						Workset.add(succ);
					}  
				}
			}
		}
		State out = new State();
		for (Unit u : g.getBody().getUnits()) {
			if (g.getSuccsOf(u).isEmpty()) {
				out.copy(inUnits.get(u));
				break;
			}
		}
	    return out;
		
	}

	public static State mergeChanges(State state_1, State state_2) {
		// Create a new state object to hold the merged state
		State merged = new State();
		
		// Merge the stack maps from state_1 and state_2
		for (String key : state_1.stack.keySet()) {
			if (state_2.stack.containsKey(key)) {
				// If the key exists in both states, merge their sets
				Set<String> unionSet = new HashSet<>(state_1.stack.get(key));
				unionSet.addAll(state_2.stack.get(key));
				merged.stack.put(key, unionSet);
			} else {
				// If the key exists only in state_1, copy its set
				merged.stack.put(key, state_1.stack.get(key));
			}
		}
		
		// Add keys from state_2 that are not present in state_1
		for (String key : state_2.stack.keySet()) {
			if (!state_1.stack.containsKey(key)) {
				merged.stack.put(key, state_2.stack.get(key));
			}
		}
		
		// Merge the heap maps from state_1 and state_2
		for (String key : state_1.heap.keySet()) {
			if (state_2.heap.containsKey(key)) {
				// If the key exists in both states, merge their sets
				Set<String> unionSet = new HashSet<>(state_1.heap.get(key));
				unionSet.addAll(state_2.heap.get(key));
				merged.heap.put(key, unionSet);
			} else {
				// If the key exists only in state_1, copy its set
				merged.heap.put(key, state_1.heap.get(key));
			}
		}
		
		// Add keys from state_2 that are not present in state_1
		for (String key : state_2.heap.keySet()) {
			if (!state_1.heap.containsKey(key)) {
				merged.heap.put(key, state_2.heap.get(key));
			}
		}
		
		// Return the merged state object
		return merged;
	}



	List<String> getEscape(State out) {
		Set<String> AllEscape = new HashSet<>(escapeObjs);
		// I have some Escaping objects in escapeObjs, from heap, find the reachable objects and add them to AllEscape 
		// Add until size of All Escape doesn't change 
		// Add 
		while (true) {
			int size = AllEscape.size();
			Set<String> TempEscape = new HashSet<>(AllEscape);
			// put all escaped objects in TempEscape
			for (String escape : TempEscape) {
				for (String key : out.heap.keySet()) {

					// print value 
					// if key has part of escape then add all values to AllEscape
					if (key.contains(escape)) {
						AllEscape.addAll(out.heap.get(key));
					}
					
				}
			}
			if (size == AllEscape.size()) {
				break;
			}
		}
		// remove Oglob if present and sort AllescapeObjs 
		AllEscape.remove("Oglob");
		List<String> sorted = new ArrayList<>(AllEscape);

		// Parse strings into integers
		List<Integer> integers = new ArrayList<>();
		for (String s : sorted) {
			// Remove letter 'O' from the string and parse it as an integer
			int value = Integer.parseInt(s.replace("O", ""));
			integers.add(value);
		}

		// Sort the integers
		Collections.sort(integers);

		// Convert sorted integers back to strings
		List<String> ans = new ArrayList<>();
		for (int value : integers) {
			// Convert integer back to string and add it to the list
			ans.add(String.valueOf(value));
		}


		// print all escaped objects
		return ans; 
	}



	private static void getlistofMethods(SootMethod method, Set<SootMethod> reachableMethods) {
        // Avoid revisiting methods
        if (reachableMethods.contains(method)) {
            return;
        }
        // Add the method to the reachable set
        reachableMethods.add(method);

        // Iterate over the edges originating from this method
        Iterator<Edge> edges = Scene.v().getCallGraph().edgesOutOf(method);
        while (edges.hasNext()) {
            Edge edge = edges.next();
            SootMethod targetMethod = edge.tgt();
            // Recursively explore callee methods
            if (!targetMethod.isJavaLibraryMethod()) {
                getlistofMethods(targetMethod, reachableMethods);
            }
        }
    }
	

	// get pointsTo information from heap for an object 
	public Set<String> getPointsTo(String objNo, State OUT) {
		Set<String> pointsTo = new HashSet<>();
		// get these values until the size of pointsTo doesn't change
		for (String key : OUT.heap.keySet()) {
			if (key.contains(objNo)) {
				pointsTo.addAll(OUT.heap.get(key));
			}
		}


		while (true) {
			int size = pointsTo.size();
			Set<String> temp = new HashSet<>(pointsTo);
			for (String obj : temp) {
				for (String key : OUT.heap.keySet()) {	
					if (key.contains(obj)) {
						pointsTo.addAll(OUT.heap.get(key));
					}
				}
			}
			if (size == pointsTo.size()) {
				break;
			}
		}


		return pointsTo;
	}

	// get <ObjNo=String, Vars= Set> using stack and heap of OUT 
	public HashMap<String, Set<String>> getObjVars(State OUT) {


		// Using Stack <Var=String, ObjNo=Set> get <ObjNo=String, Vars= Set> 
		HashMap<String, Set<String>> objVars = new HashMap<>();
		for (String var : OUT.stack.keySet()) {
			Set<String> objNos = OUT.stack.get(var);
			for (String objNo : objNos) {
				if (!objVars.containsKey(objNo)) {
					objVars.put(objNo, new HashSet<>());
				}
				objVars.get(objNo).add(var);
			}
		}
		// Uset pointsTo information from heap and add to objVars 
		HashMap<String, Set<String>> tempVars = objVars; 
		// For each of tempVars objects get its pointsTo's vars and add to objVars 
		for (String objNo : tempVars.keySet()) {
			// print vars 
			Set<String> pointsTo = getPointsTo(objNo, OUT);
			
			// Entirity of pointsTo objects will have same vars 
			for (String pointToObj : pointsTo) {
				Set<String> tempObjs = tempVars.get(pointToObj);
				// add tempObjs to objVars 
				objVars.get(objNo).addAll(tempObjs);

			}

			for (String pointToObj: pointsTo) {
				objVars.get(pointToObj).addAll(objVars.get(objNo));
			}

			// for (String pointToObj : pointsTo) {
			// 	Set<String> tempObjs = tempVars.get(pointToObj);
			// 	// add tempObjs to objVars 
			// 	objVars.get(objNo).addAll(tempObjs);

			// }
		}
		
	

		return objVars;
	}

	public List<Local> findMissingVariables(List<Local> liveBefore, List<Local> liveAfter) {
        List<Local> missingVariables = new ArrayList<>();
        for (Local variable : liveBefore) {
            if (!liveAfter.contains(variable)) {
				// print variable, liveBefore, liveAfter 
                missingVariables.add(variable);
            }
        }
        return missingVariables;
    }


	public HashMap<String, Set<String>> garbageCollect(SootMethod m) {
		Body body = m.getActiveBody();
		UnitGraph cfg = new BriefUnitGraph(body); 
		LiveLocals liveLocals = new SimpleLiveLocals(cfg);

		PatchingChain<Unit> units = body.getUnits(); 

		HashMap<String, Set<String>> escapeGC = new HashMap<>();

		String funcName = body.getMethod().getDeclaringClass().getName() + ":"+ body.getMethod().getName().toString(); 

		if(m.isConstructor()) return escapeGC;


		State OUT = IntraEscapeAnalysis(body, new State());
		// Here after IntraEscape and get HashMap<ObjNo=String, Vars= Set> using stack and heap of OUT
		OUT.print(); 

		escapeGC = getObjVars(OUT);

		// Print escapeGC 
		System.out.println("EscapeGC Init : " + escapeGC);

		Map<String, Integer> variableCounts = new HashMap<>();

        // Iterate over units
        for (Unit u : units) {
            // Get live variables before the unit
            List<Local> liveBefore = liveLocals.getLiveLocalsBefore(u);
			List<Local> liveAfter = liveLocals.getLiveLocalsAfter(u);
			List<Local> missingVariables = findMissingVariables(liveBefore, liveAfter);

            // Update count for each live variable
            for (Local local : missingVariables) {
                String variableName = local.getName();
                variableCounts.put(variableName, variableCounts.getOrDefault(variableName, 0) + 1);
            }
        }


		// iterate over units and using getEdgesOutof get various methods called 
		for (Unit u : units) {

			// if u is of return then skip 
			if (u instanceof ReturnStmt) {
				continue;
			}
			
			// live variables before and after the unit and keep removing from escapeGC 

			// get live variables before the unit
			List<Local> liveBefore = liveLocals.getLiveLocalsBefore(u);
			List<Local> liveAfter = liveLocals.getLiveLocalsAfter(u);

			// print liveBefore 
			List<Local> missingVariables = findMissingVariables(liveBefore, liveAfter);

			// print before, after missing 
			// System.out.println("Before : " + liveBefore + " After : " + liveAfter + " Missing : " + missingVariables + u + u.getJavaSourceStartLineNumber());

			// remove liveBefore from escapeGC 
			for (Local live : missingVariables) {
				String var = live.toString();

				// hardcopy escapeGC into tempGC 

				// reduce count of variable in variableCounts 
				variableCounts.put(var, variableCounts.get(var) - 1);
				

				// if count of variable is 0 then remove from escapeGC 
				if (variableCounts.get(var) == 0) {
					for (String key : escapeGC.keySet()) {
						if (escapeGC.get(key).contains(var)) {
							escapeGC.get(key).remove(var);

							if (escapeGC.get(key).isEmpty() ) {
								// add to garbageObjs 
								// get line number and convert to string 
								// print key, u.getJavaSourceStartLineNumber(), u 
								// System.out.println("Garbage : " + key + " " + u.getJavaSourceStartLineNumber() + " " + u + " Var : " + var);
								// print escapeGC
								// System.out.println("GarbageGC : " + escapeGC);

								garbageObjs.put(key,String.valueOf (u.getJavaSourceStartLineNumber() + "_" + funcName));
							}
							
						}
					}
				}
				

			}
			
			// get the edges out of the unit,  merge results  
			for (Iterator<Edge> edges = cg.edgesOutOf(u); edges.hasNext(); ) {
				// Print unit only once 

				Edge edge = edges.next();
				SootMethod targetMethod = edge.tgt();
				if (targetMethod.isJavaLibraryMethod() || targetMethod.isConstructor()) {
					continue;
				}
				// Here need to call Intra Analysis and merge 
				// Print Unit and targetMethod 
				// System.out.println("Unt : " + u + " TargetMethod : " + targetMethod); 
				// Here better to call garbageCollect and then IntraEscapeAnalysis inside it assuming recursively.
				// Garbage collect and store escapeGC 
				HashMap<String, Set<String>> temp = garbageCollect(targetMethod);

				// From temp get all keys which contain Oglob and add key, oglob<some_val> to escapeGC 
				State tempOut = IntraEscapeAnalysis(targetMethod.getActiveBody(), new State()); 

				// collect return values from temp 
				for (String key : temp.keySet()) {
					if(!key.contains("Oglob")) {
						// if temp.get(key) is empty continue 
						if (temp.get(key).isEmpty()) {
							continue;
						}

						// get return left stmt if present else assign garbageObjs to current line number

						// check whether current unit has return object to store to 
						// if not then store garbageObjs to current line number
						// print u, characteristics of u 
						// System.out.println("Unit Return : " + u + " Line No : " + u.getJavaSourceStartLineNumber() + " Class : " + u.getClass()); 
						if (u instanceof ReturnStmt) {
							ReturnStmt stmt = (ReturnStmt) u;
							Value ret = stmt.getOp();
							if (ret instanceof Local) {
								Local retLocal = (Local) ret;
								// add {key : retLocal} to escapeGC
								if (!escapeGC.containsKey(key)) {
									escapeGC.put(key, new HashSet<>());
								}
								escapeGC.get(key).add(retLocal.toString());
							}
						} else {
							// add {key : lineNo} to garbageObjs 
							garbageObjs.put(key, String.valueOf(u.getJavaSourceStartLineNumber() +"_" +funcName )); 
						}
					}
				}


				// get parameters of targetMethod
				List<Local> parameters = targetMethod.getActiveBody().getParameterLocals();
				// print parameters
				// System.out.println("Parameters : " + parameters);
					// get the unit and get args

				List<Value> args ;
				if (u instanceof JAssignStmt) {
					JAssignStmt stmt = (JAssignStmt) u;
					Value right = stmt.getRightOp();
					if (right instanceof InvokeExpr) {
						InvokeExpr expr = (InvokeExpr) right;
						args = expr.getArgs();
					} else {
						args = new ArrayList<>();
					}
				} else {
					InvokeStmt stmt = (InvokeStmt) u;
					InvokeExpr expr = stmt.getInvokeExpr();
					args = expr.getArgs();
				}

				// Parse unsing integer for index 
				for (int i = 0; i < parameters.size(); i++) {
					// get pointsTo information from heap for an object
					Set<String> pointsTo = getPointsTo("Oglob_" + parameters.get(i), tempOut);
					// add {pointsToVars : Arg[i]} to escapeGC
					for (String pointsToVar : pointsTo) {
						// if count of args[i] in variableCounts is nonZero then add to escapeGC 
						if (variableCounts.get(args.get(i).toString()) != 0) {
							if (!escapeGC.containsKey(pointsToVar)) {
								escapeGC.put(pointsToVar, new HashSet<>());
							}
							escapeGC.get(pointsToVar).add(args.get(i).toString());
						// System.out.println("PointsToGC : " + pointsTo + " Args : " + args.get(i) + " PointsToVar : " + pointsToVar + " EscapeGC : " + escapeGC);
						}
					}
				}
				// print escapeGC 
				// System.out.println("EscapeGCNew : " + escapeGC);
				
			
				// print args
				// System.out.println("Args : " + args);


			}
		}

		// Print escapeGC and garbageObjs 
		// System.out.println("PointsToGlobal : " + getPointsTo("Oglob", OUT));
		System.out.println("EscapeGC : " + escapeGC);
		System.out.println("GarbageObjs : " + garbageObjs);

		return escapeGC;
		

	}

	// create a function to merge two HashMap<String, Set<String>> 
	public HashMap<String, Set<String>> mergeGC(HashMap<String, Set<String>> gc1, HashMap<String, Set<String>> gc2) {
		HashMap<String, Set<String>> merged = new HashMap<>();
		for (String key : gc1.keySet()) {
			if (gc2.containsKey(key)) {
				Set<String> unionSet = new HashSet<>(gc1.get(key));
				unionSet.addAll(gc2.get(key));
				merged.put(key, unionSet);
			} else {
				merged.put(key, gc1.get(key));
			}
		}
		for (String key : gc2.keySet()) {
			if (!gc1.containsKey(key)) {
				merged.put(key, gc2.get(key));
			}
		}
		return merged;
	}
	

	public void printGarbageDetails() { 
		// sort garbageoBjs is map <ObjNo=String, LineNo=String> 
		// I want to sort by lineNo

		// print garbageObjs 
		// System.out.println("GarbageObjs : " + garbageObjs);

		// Hash<FuncName, "objNO: GarbageNO"> 
		HashMap<String, String> garbageFunc = new HashMap<>();

		for (String key : garbageObjs.keySet()) {
			String[] parts = garbageObjs.get(key).split("_");
			String lineNo = parts[0];
			String funcName = parts[1];
			if (!garbageFunc.containsKey(funcName)) {
				garbageFunc.put(funcName, key + ":" + lineNo);
			} else {
				String val = garbageFunc.get(funcName);
				val += " " + key + ":" + lineNo;
				garbageFunc.put(funcName, val);
			}
		}

		// Print garbageFunc
		// System.out.println("GarbageFunc : " + garbageFunc);

		// remove if value starts with Oglob, and remove first character from the value and modify garbageFunc map 
		HashMap<String, String> garbageFuncNew = new HashMap<>();
		for (String key : garbageFunc.keySet()) {
			String val = garbageFunc.get(key);
			String[] parts = val.split(" ");
			String newVal = "";
			for (String part : parts) {
				if (!part.startsWith("Oglob")) {
					newVal += part.substring(1) + ",";
				}
			}
			if (!newVal.isEmpty()) {
				newVal = newVal.substring(0, newVal.length() - 1);
				garbageFuncNew.put(key, newVal);
			}
		}

		// Print garbageFuncNew
		// System.out.println("GarbageFuncNew : " + garbageFuncNew);
		
		// Sort the space separated values and store in garbageFuncFinal 
		HashMap<String, String> garbageFuncFinal = new HashMap<>();
		for (String key : garbageFuncNew.keySet()) {
			String val = garbageFuncNew.get(key);
			String[] parts = val.split(",");
			Arrays.sort(parts);
			String newVal = "";
			for (String part : parts) {
				newVal += part + " ";
			}
			garbageFuncFinal.put(key, newVal);
		}

		// Print garbageFuncFinal
		// System.out.println("GarbageFuncFinal : " + garbageFuncFinal);

		SootMethod m = Scene.v().getMainMethod(); 
		Set<SootMethod> methods = new HashSet <>();
		getlistofMethods(m, methods);

		// Sort methods by method.getActiveBody().getMethod().getDeclaringClass().getName() + ":" + method.getActiveBody().getMethod().getName().toString() 
		

		// Iterate through methods and create a List of names of the format "ClassName:MethodName"
		List<String> methodNames = new ArrayList<>();
		for (SootMethod method : methods) {
			if (method.isJavaLibraryMethod() || method.isConstructor()) {
				continue;
			}


			methodNames.add(method.getActiveBody().getMethod().getDeclaringClass().getName() + ":" + method.getActiveBody().getMethod().getName().toString());
		}
		// Sort methodNames 
		Collections.sort(methodNames);


		// Print sortedMethods
		// System.out.println("SortedMethods : " + methodNames);

		// Print garbageFuncFinal using sortedMethods 
		for (String method : methodNames) {
			if (garbageFuncFinal.containsKey(method)) {
				System.out.println(method + " " + garbageFuncFinal.get(method));
			} else 
				System.out.println(method);
		}



		
	}
	

    @Override
    public synchronized void internalTransform(String phaseName, Map<String, String> options) {
        // Construct CFG for the current method's body
       
		escapeObjs.clear();
		
		cg = Scene.v().getCallGraph();

		// generateCallGraph(cg, "callgraph.dot");

		// InterProcess(cg);

		SootMethod m = Scene.v().getMainMethod(); 

		garbageCollect(m);

		// State OUT = IntraEscapeAnalysis(m.getActiveBody(), new State());

		Set<SootMethod> methods = new HashSet <>();

		getlistofMethods(m, methods);

		// for (SootMethod method : methods) {
		// 	if (method.isJavaLibraryMethod() || method.isConstructor()) {
		// 		continue;
		// 	}

		// print garbage Details 
		printGarbageDetails();

		// 	State OUT = IntraEscapeAnalysis(method.getActiveBody(), new State());
		// 	System.out.println("Method : " + method.getSignature());
		// 	OUT.print();

		// 	// get pointsTo information from heap for an object
		// 	Set<String> pointsTo = getPointsTo("O9", OUT);
		// 	System.out.println("PointsTo : " + pointsTo);

		// 	// get <ObjNo=String, Vars= Set> using stack and heap of OUT 
		// 	HashMap<String, Set<String>> objVars = getObjVars(OUT);
		// 	System.out.println("ObjVars : " + objVars);
		// }


		// Sort methodEscape by key 

		escapeObjs.clear();

		// for (SootMethod method : methods) {
		// 	processCFG(method);
		// }



    }



}
