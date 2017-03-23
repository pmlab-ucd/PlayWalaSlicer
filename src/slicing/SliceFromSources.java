/*
Sourced from http://wala.sourceforge.net/wiki/index.php/UserGuide:Slicer
and slightly modified

Original sources can be found at
https://github.com/SCanDroid/WALA/blob/master/com.ibm.wala.core.tests/src/com/ibm/wala/examples/drivers/PDFSlice.java
https://github.com/wala/WALA/blob/master/com.ibm.wala.core.tests/src/com/ibm/wala/examples/drivers/PDFWalaIR.java
*/
package slicing;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.*;
import com.ibm.wala.ipa.callgraph.impl.Util;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.slicer.NormalReturnCaller;
import com.ibm.wala.ipa.slicer.NormalStatement;
import com.ibm.wala.ipa.slicer.Slicer;
import com.ibm.wala.ipa.slicer.Slicer.ControlDependenceOptions;
import com.ibm.wala.ipa.slicer.Slicer.DataDependenceOptions;
import com.ibm.wala.ipa.slicer.Statement;
import com.ibm.wala.ipa.slicer.Statement.Kind;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAAbstractInvokeInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAInvokeInstruction;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeReference;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.intset.IntSet;
import com.ibm.wala.util.strings.Atom;

import java.io.*;
import java.util.*;

public class SliceFromSources {

    private static final int PRINT_LIMIT = 5;
    // this is a place where we could cut things down to improve scalability
    private static File EXCLUSIONS = getExclusionsFile();

    /**
     * Build call graph builder with specific analysis algorithm
     * @param analysis
     * @param options
     * @param cache
     * @param cha
     * @param scope
     * @return
     */
    public static CallGraphBuilder makeCallGraphBuilder(
            String analysis,
            AnalysisOptions options,
            AnalysisCache cache,
            ClassHierarchy cha,
            AnalysisScope scope) {

        CallGraphBuilder builder = null;

        switch(analysis) {
            case "0cfa":
                builder = Util.makeZeroCFABuilder(options, cache, cha, scope, null, null);
                break;
            case "vanilla-1cfa":
                builder = Util.makeVanillaZeroOneCFABuilder(options, cache, cha, scope, null, null);
                break;
            case "container-1cfa":
                builder = Util.makeZeroOneContainerCFABuilder(options, cache, cha, scope);
                break;
            default:
                System.out.println("Unknown analysis");
                System.exit(1);
        }

        return builder;
    }

    /**
     * Run forward slicing
     * @param appJar
     * @param analysis
     */
    public static void slice(String appJar, String analysis) {
        try {
            // naive timing, but fine for example purposes
            final long startTime = System.currentTimeMillis();

            AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar, EXCLUSIONS);

            // create class hierarchy, wala needs to know the lay of the land
            System.out.println("Building hierarchy");
            ClassHierarchy cha = ClassHierarchy.make(scope);
            Iterable<Entrypoint> entrypoints = Util.makeMainEntrypoints(scope, cha);
            AnalysisOptions options = new AnalysisOptions(scope, entrypoints);


            // build the call graph
            System.out.println("Building call graph");
            CallGraphBuilder builder = makeCallGraphBuilder(analysis, options, new AnalysisCache(), cha, scope);
            CallGraph cg = builder.makeCallGraph(options, null);
            // pointer analysis
            PointerAnalysis pa = builder.getPointerAnalysis();


            // data and control flow dependencies (for reachability) in slicing
            DataDependenceOptions dataOptions = DataDependenceOptions.FULL;
            ControlDependenceOptions controlOptions = ControlDependenceOptions.FULL;

            // collecting any methods that implement taint sources
            System.out.println("Collecting taint source implementors");
            Set<MethodReference> sources = new HashSet<>();
            sources.addAll(subclassImplementors(cha, "Ljava/io/InputStream", "read", TypeReference.Int));


            // find all callers in application code that call any of our taint sources
            System.out.println("Collecting callers of taint sources in application");
            Map<MethodReference, Set<CGNode>> callerNodes = new HashMap<>();
            for(MethodReference source : sources) {
                Set<CGNode> callersForSource = findApplicationCallers(cg, source);
                if (callerNodes.containsKey(source)){
                    callerNodes.get(source).addAll(callersForSource);
                } else {
                    callerNodes.put(source, callersForSource);
                }
            }

            // find all call sites
            System.out.println("Collecting call sites for taint sources");
            List<Statement> calls = new ArrayList<Statement>();
            for (MethodReference source : callerNodes.keySet()) {
                for(CGNode caller : callerNodes.get(source)) {
                    calls.addAll(findCallSites(caller, source));
                }
            }

            // find all return statements for calls
            List<Statement> returns = new ArrayList<>();
            for (Statement call : calls) {
                returns.add(getReturnStatementForCall(call));
            }

            System.out.println("Collected " + returns.size() + " return sites to use as criteria for slicing");

            // collect forwards
            List<Statement> slices = new ArrayList<>();
            for(Statement ret : returns) {
                System.out.println("===> Computing slice");
                Collection<Statement> slice = Slicer.computeForwardSlice(ret, cg, pa, dataOptions, controlOptions);
                slices.addAll(slice);
                System.out.println("===> Done with slice");
            }

            // note that the two print statements above are factoring into this time
            final long endTime = System.currentTimeMillis();
            System.out.println("Collected " + slices.size() + " statements in slices");
            report(analysis, endTime - startTime);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    // get exclusions for analysis
    public static File getExclusionsFile() {
        // read file from jar and put it into a temp file
        try {
            InputStream resource =
                    SliceFromSources.class.getClassLoader().getResourceAsStream("exclusions.txt");
            File tempfile = File.createTempFile("exclusions", ".txt");
            OutputStream out = new FileOutputStream(tempfile);
            int read = 0;
            byte[] data = new byte[1024];

            while((read = resource.read(data)) != -1) {
                out.write(data, 0, read);
            }
            tempfile.deleteOnExit();
            return tempfile;
        } catch (IOException e) {
            e.printStackTrace();
        }
        return null;
    }


    // find methods that perform a call to method mr in the callgraph cg
    // and are loaded with the application class loader
    public static Set<CGNode> findApplicationCallers(CallGraph cg, MethodReference mr) {
        Set<CGNode> callers = new HashSet<>();
        for (Iterator<CGNode> it = cg.iterator(); it.hasNext();) {
            CGNode callee = it.next();
            if (callee.getMethod().getReference().equals(mr)) {
                for(Iterator<CGNode> callerIt = cg.getPredNodes(callee); callerIt.hasNext(); ) {
                    CGNode next = callerIt.next();
                    // only interested in callers in application code
                    if (next.getMethod().getDeclaringClass().getClassLoader().getReference().equals(ClassLoaderReference.Application)) {
                        callers.add(next);
                    }
                }
            }
        }
        return callers;
    }

    /**
     * Given a class, find all concrete subclasses, and return method references
     * for methods that have the appropriate return type and a method name that
     * starts with the appropriate prefix
     * @param ch
     * @param baseClassName
     * @param methodNameprefix
     * @param returnType
     * @return
     */
    public static Set<MethodReference>
    subclassImplementors(ClassHierarchy ch,
                         String baseClassName,
                         String methodNameprefix,
                         TypeReference returnType) {
        System.out.println("Collecting subclass methods for " + baseClassName);
        Set<MethodReference> methods = new HashSet<>();

        TypeReference base = TypeReference.findOrCreate(ClassLoaderReference.Primordial, baseClassName);
        Collection<IClass> subclasses = ch.computeSubClasses(base);
        Atom methodNameStart = Atom.findOrCreateAsciiAtom(methodNameprefix);

        for(IClass subclass : subclasses) {
            // we only collect method references for non-abstract classes
            if(!subclass.isAbstract()) {
                // collect
                for (IMethod method : subclass.getAllMethods()) {
                    // right return type and starts qwith appropriate name
                    // FIXME
                    //if(method.getReturnType().equals(returnType) &&
                      //      method.getSelector().getName().startsWith(methodNameStart)) {
                        //methods.add(method.getReference());
                    //}
                }
            }
        }

        return methods;
    }


    // find all call sites targeting method in a given call graph node
    public static List<Statement> findCallSites(CGNode n, MethodReference method) {
        System.out.println("Looking for call to " + method.getSignature() + " in " + n.getMethod().getSignature());
        List<Statement> statements = new ArrayList<>();
        IR ir = n.getIR();
        for (Iterator<SSAInstruction> it = ir.iterateAllInstructions(); it.hasNext();) {
            SSAInstruction s = it.next();
            if (s instanceof SSAInvokeInstruction) {
                SSAInvokeInstruction call = (SSAInvokeInstruction) s;
                if (call.getCallSite().getDeclaredTarget().getDescriptor().equals(method.getDescriptor())) {
                    System.out.println("Found call site for " + method.getSignature());
                    IntSet indices = ir.getCallInstructionIndices(((SSAInvokeInstruction) s).getCallSite());
                    Assertions.productionAssertion(indices.size() == 1, "expected 1 but got " + indices.size());
                    Statement callStmt = new NormalStatement(n, indices.intIterator().next());
                    statements.add(callStmt);
                }
            }
        }
        if (statements.size() == 0) {
            Assertions.UNREACHABLE("failed to find call to " + method.toString() + " in " + n);
        }
        return statements;
    }

    // modification of original to use method reference
    // get return statement associated with call
    public static Statement getReturnStatementForCall(Statement s) {
        if (s.getKind() == Kind.NORMAL) {
            NormalStatement n = (NormalStatement) s;
            SSAInstruction st = n.getInstruction();
            if (st instanceof SSAInvokeInstruction) {
                SSAAbstractInvokeInstruction call = (SSAAbstractInvokeInstruction) st;
                if (call.getCallSite().getDeclaredTarget().getReturnType().equals(TypeReference.Void)) {
                    throw new IllegalArgumentException("this driver computes forward slices from the return value of calls.\n" + ""
                            + "Method " + call.getCallSite().getDeclaredTarget().getSignature() + " returns void.");
                }
                return new NormalReturnCaller(s.getNode(), n.getInstructionIndex());
            } else {
                return s;
            }
        } else {
            return s;
        }
    }

    /**
     * Provide reporting of execution time
     * @param analysis
     * @param ms
     */
    public static void report(String analysis, long ms) {
        System.out.println("\n\t" + analysis + ": " + ms + " ms");
    }

    /**
     * Help message
     */
    public static void help() {
        System.out.println(
                "Usage:java -jar slicer.java slicing.SliceFromSources <target-jar-path> <analysis>\n" +
                        "Analysis must be one of: 0cfa, vanilla-1cfa, container-1cfa\n" +
                        "For example:\n" +
                        "slicing.SliceFromSources example.jar 0cfa\n"
        );
    }

    /**
     * Run experiment on a given jar + caller + callee + analysis
     * @param args
     */
    public static void main(String[] args) {
        List<String> analysisNames = Arrays.asList("0cfa", "vanilla-1cfa", "container-1cfa");
        if (args.length != 2) {
            help();
            System.exit(1);
        }

        String jarPath = args[0];
        String analysis = args[1];

        if (!analysisNames.contains(analysis)) {
            help();
            System.exit(1);
        }

        slice(jarPath, analysis);
    }
}