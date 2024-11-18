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
// import javafx.util.Pair;
import soot.util.*;
import java.io.File;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.io.IOException;



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
	

public class AnalysisTransformer extends BodyTransformer {

	// Map of method Name and set of escaping objects
	static Map<String, List<String>> methodEscape = new HashMap<>(); 
	
	// Set of all escaped Objects	
	static Set<String> escapeObjs =  new HashSet<>();
	

	static Map<Unit,String>allocationSite = new HashMap<>();
	
	
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
		// if (u.getJavaSourceStartLineNumber() == 50) {
		// 	System.out.println("LineStart 50: " + u);
		// 	System.out.println("Class 10: " + u.getClass());
		// }
		
		
		State out = new State(); 
		out.copy(inUnits);
		
		
		
		if(u instanceof DefinitionStmt) {
			
			DefinitionStmt st = (DefinitionStmt) u;
			Value rightStmt = st.getRightOp();
			Value leftStmt =st.getLeftOp();

			// line number 13 print details
			// if (u.getJavaSourceStartLineNumber() == 50) {
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
					out.stack.put(leftStmt.toString(),values);	
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

			// X = foo(a,b,c); 
			else if (rightStmt instanceof VirtualInvokeExpr) {
				// make args of rightStmt to escape 
				// System.out.println("X = foo() Line No : " + u.getJavaSourceStartLineNumber() + " X_base : " + leftStmt + " Y_base : " + rightStmt + " Unit : " + u + "Stack : " + inUnits.stack);
				VirtualInvokeExpr invokeExpr = (VirtualInvokeExpr) rightStmt;
				List<Value> args = invokeExpr.getArgs();
				for (Value arg : args) {
					if (inUnits.stack.containsKey(arg.toString())) {
						escapeObjs.addAll(inUnits.stack.get(arg.toString()));
					}
				}
				// check if rightstmt is a.foo(b,c)
				// get a from invokeExpr 
				Value base = invokeExpr.getBase(); 
				// Escape base 
				if (inUnits.stack.containsKey(base.toString())) {
					escapeObjs.addAll(inUnits.stack.get(base.toString()));
				}

				// make left stmt escape
				Set<String> ref = new HashSet<>();
				ref.add("Oglob");
				// if leftStmt is Local then add to stack else
				if (leftStmt instanceof Local) {
					out.stack.put(leftStmt.toString(), ref);
				} 
			}

			else if (rightStmt instanceof ParameterRef){ 
				// Add to stack and escape as Oglob 
				Set<String> ref = new HashSet<>();
				ref.add("Oglob");
				out.stack.put(leftStmt.toString(), ref);
				escapeObjs.addAll(ref);

			}

			// .this variable 
			else if (rightStmt instanceof ThisRef){
				// Add to stack and escape as Oglob 
				Set<String> ref = new HashSet<>();
				ref.add("Oglob");
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
			// Other than constructors 
			if(!u.toString().contains("init") ) {
				

				// Print if lineNumber = 18 
				// if (u.getJavaSourceStartLineNumber() == 50) {
				// 	System.out.println("Invoke 50: ");
				// 	System.out.println("Line 50: " + u);
				// 	System.out.println("Class 18: " + u.getClass());
				// }

				String method = u.toString();

				// Make args of method to escape 
				InvokeStmt stmt = (InvokeStmt) u;
				InvokeExpr expr = stmt.getInvokeExpr();
				List<Value> args = expr.getArgs();
				// print args 
				// System.out.println("InvokeArgs: " + args + " expr " + expr.toString());

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

				}
				// for arraylist methods
				if (expr instanceof JInterfaceInvokeExpr) {
					JInterfaceInvokeExpr virtualInvokeExpr = (JInterfaceInvokeExpr) expr;
					base = virtualInvokeExpr.getBase();
					if (inUnits.stack.containsKey(base.toString())) {
						escapeObjs.addAll(inUnits.stack.get(base.toString()));
					}

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


    @Override
    public synchronized void internalTransform(Body body, String phaseName, Map<String, String> options) {
        // Construct CFG for the current method's body
       
		escapeObjs.clear();


       State OUT =IntraEscapeAnalysis(body, new State());

        // OUT.print();
		List<String> escapeVals = getEscape(OUT);
		// Add ClasName + method name and escaped objects to methodEscape
		// System.out.println("Escape : " + escapeObjs);

		// methodEscape.put( body.getMethod().getName().toString() + ":" + body.getMethod().getDeclaringClass().getName(), escapeVals);
		methodEscape.put( body.getMethod().getDeclaringClass().getName() + ":"+ body.getMethod().getName().toString() , escapeVals);

		// Sort methodEscape by key 

		escapeObjs.clear();





    }
}
