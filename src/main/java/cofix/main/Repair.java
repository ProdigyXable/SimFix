/**
 * Copyright (C) SEI, PKU, PRC. - All Rights Reserved.
 * Unauthorized copying of this file via any medium is
 * strictly prohibited Proprietary and Confidential.
 * Written by Jiajun Jiang<jiajun.jiang@pku.edu.cn>.
 */
package cofix.main;

import cofix.common.config.Constant;
import cofix.common.inst.Instrument;
import cofix.common.inst.MethodInstrumentVisitor;
import cofix.common.junit.runner.JUnitEngine;
import cofix.common.junit.runner.JUnitRuntime;
import cofix.common.junit.runner.OutStream;
import cofix.common.localization.AbstractFaultlocalization;
import cofix.common.run.Runner;
import cofix.common.util.JavaFile;
import cofix.common.util.Pair;
import cofix.common.util.Status;
import cofix.common.util.Subject;
import cofix.core.match.CodeBlockMatcher;
import cofix.core.modify.Modification;
import cofix.core.modify.Revision;
import cofix.core.parser.NodeUtils;
import cofix.core.parser.node.CodeBlock;
import cofix.core.parser.node.Node;
import cofix.core.parser.search.BuggyCode;
import cofix.core.parser.search.SimpleFilter;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Pattern;
import org.apache.commons.io.FileUtils;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.FieldAccess;
import org.eclipse.jdt.core.dom.Name;
import org.eclipse.jdt.core.dom.Type;
import org.junit.runner.Result;
import utdallas.edu.profl.replicate.patchcategory.DefaultPatchCategories;
import utdallas.edu.profl.replicate.util.ProflResultRanking;
import utdallas.edu.profl.replicate.util.XiaMethodLineCoverage;
import utdallas.edu.profl.replicate.util.XiaTestLineCoverage;
import utdallas.edu.profl.replicate.util.interfaces.MethodLineCoverageInterface;
import utdallas.edu.profl.replicate.util.interfaces.TestLineCoverageInterface;

/**
 * @author Jiajun
 * @date Jun 20, 2017
 */
public class Repair {

    private int patchAttempts = 0;
    private AbstractFaultlocalization _localization = null;
    private Subject _subject = null;
    private List<String> _failedTestCases = null;
    private List<String> _passedTestCases = null;
    private Map<Integer, Set<Pair<String, String>>> _passedTestCasesMap = null;

    final private TestLineCoverageInterface testCoverage;
    final private MethodLineCoverageInterface methodCoverage;
    final private ProflResultRanking profl;

    public Repair(Subject subject, AbstractFaultlocalization fLocalization) throws Exception {
        _localization = fLocalization;
        _subject = subject;
        _failedTestCases = fLocalization.getFailedTestCases();
        _passedTestCases = fLocalization.getPassedTestCases();
        _passedTestCasesMap = new HashMap<>();

        String testCoveragePath = Constant.PROFL_TEST;
        String methodCoveragePath = Constant.PROFL_METHOD;
        String failingTestPath = Constant.PROFL_FAIL;

        testCoverage = new XiaTestLineCoverage(testCoveragePath);
        methodCoverage = new XiaMethodLineCoverage(methodCoveragePath);
        profl = new ProflResultRanking(methodCoverage, testCoverage, failingTestPath);
        profl.outputSbflSus();
    }

    private void computeMethodCoverage() throws IOException {
        JUnitRuntime runtime = new JUnitRuntime(_subject);
        String src = _subject.getHome() + _subject.getSsrc();
        MethodInstrumentVisitor methodInstrumentVisitor = new MethodInstrumentVisitor();
        Instrument.execute(src, methodInstrumentVisitor);

        if (!Runner.compileSubject(_subject)) {
            System.err.println("Build project failed!");
            System.exit(0);
        }

        System.out.println("Passed test classes : " + _localization.getPassedTestCases().size());
        for (String test : _localization.getPassedTestCases()) {
            String[] testStr = test.split("#");
            String clazz = testStr[0];
            String methodName = testStr[1];
            OutStream outStream = new OutStream();
            Result result = JUnitEngine.getInstance(runtime).test(clazz, methodName, new PrintStream(outStream));
            if (result.getFailureCount() > 0) {
                System.out.println("Error : Passed test cases running failed ! => " + clazz);
                System.exit(0);
            }
            for (Integer method : outStream.getOut()) {
                Set<Pair<String, String>> tcases = _passedTestCasesMap.get(method);
                if (tcases == null) {
                    tcases = new HashSet<>();
                }
                tcases.add(new Pair<String, String>(clazz, methodName));
                _passedTestCasesMap.put(method, tcases);
            }
        }
        // restore source file
        _subject.restore();
    }

    public Status fix(Timer timer, String logFile, int currentTry) throws IOException {
        String src = _subject.getHome() + _subject.getSsrc();
        List<Pair<String, Integer>> locations = _localization.getLocations(2000);

        int correct = 0;
        int totalAttempts = 0;
        int locationAttempts = 0;

        Set<String> haveTryBuggySourceCode = new HashSet<>();
        Status status = Status.FAILED;
        Set<String> patches = new HashSet<>();

        for (Pair<String, Integer> loc : locations) {
            if (timer.timeout()) {
                return Status.TIMEOUT;
            }

            if (locationAttempts <= 200) {

                for (String buggyMethod : Constant.buggyMethods) {
                    String fileClass = loc.getFirst();

                    if (buggyMethod.contains(fileClass)) {
                        locationAttempts++;
                        System.out.println(String.format("Processing incorrect file: %s", fileClass));
                        _subject.restore();
                        FileUtils.deleteDirectory(new File(_subject.getHome() + _subject.getSbin()));
                        FileUtils.deleteDirectory(new File(_subject.getHome() + _subject.getTbin()));
                        // System.out.println(loc.getFirst() + "," + loc.getSecond());

                        String file = _subject.getHome() + _subject.getSsrc() + "/" + loc.getFirst().replace(".", "/") + ".java";
                        String binFile = _subject.getHome() + _subject.getSbin() + "/" + loc.getFirst().replace(".", "/") + ".class";
                        // get buggy code block
                        CodeBlock buggyblock = BuggyCode.getBuggyCodeBlock(file, loc.getSecond());
                        Integer methodID = buggyblock.getWrapMethodID();
                        if (methodID == null) {
                            // logMessage(logFile, "file=" + loc.getFirst() + ", location=" + loc.getSecond() + "=>Find no block");
                            // System.out.println("Find no block!");
                            continue;
                        }
                        // logMessage(logFile, "file=" + loc.getFirst() + ", location=" + loc.getSecond());
                        if (Constant.buggyMethods.isEmpty()) {
                            System.out.println("No buggy methods supplied!");
                            continue;
                        }

                        List<CodeBlock> buggyBlockList = new LinkedList<>();
                        buggyBlockList.addAll(buggyblock.reduce());
                        buggyBlockList.add(buggyblock);

                        for (CodeBlock oneBuggyBlock : buggyBlockList) {
                            String currentBlockString = oneBuggyBlock.toSrcString().toString();
                            if (currentBlockString == null || currentBlockString.length() <= 0) {
                                continue;
                            }
                            if (haveTryBuggySourceCode.contains(currentBlockString)) {
                                continue;
                            }
                            haveTryBuggySourceCode.add(currentBlockString);
                            _subject.restore();
                            Pair<Integer, Integer> range = oneBuggyBlock.getLineRangeInSource();
                            Set<String> haveTryPatches = new HashSet<>();
                            // get all variables can be used at buggy line
                            Map<String, Type> usableVars = NodeUtils.getUsableVarTypes(file, loc.getSecond());
                            // search candidate similar code block
                            SimpleFilter simpleFilter = new SimpleFilter(oneBuggyBlock);

                            List<Pair<CodeBlock, Double>> candidates = simpleFilter.filter(src, 0.3);
                            List<String> source = null;
                            try {
                                source = JavaFile.readFileToList(file);
                            } catch (IOException e1) {
                                System.err.println("Failed to read file to list : " + file);
                                continue;
                            }
                            int i = 1;
                            for (Pair<CodeBlock, Double> similar : candidates) {
                                // try top 100 candidates
                                if (i > 100 || timer.timeout()) {
                                    break;
                                }

                                // i++;
                                // compute transformation
                                List<Modification> modifications = CodeBlockMatcher.match(oneBuggyBlock, similar.getFirst(), usableVars);
                                Map<String, Set<Node>> already = new HashMap<>();
                                // try each transformation first
                                List<Set<Integer>> list = new ArrayList<>();
                                list.addAll(consistentModification(modifications));
                                modifications = removeDuplicateModifications(modifications);
                                for (int index = 0; index < modifications.size(); index++) {
                                    Modification modification = modifications.get(index);
                                    String modify = modification.toString();
                                    Set<Node> tested = already.get(modify);
                                    if (tested != null) {
                                        if (tested.contains(modification.getSrcNode())) {
                                            continue;
                                        } else {
                                            tested.add(modification.getSrcNode());
                                        }
                                    } else {
                                        tested = new HashSet<>();
                                        tested.add(modification.getSrcNode());
                                        already.put(modify, tested);
                                    }
                                    Set<Integer> set = new HashSet<>();
                                    set.add(index);
                                    list.add(set);
                                }

                                List<Modification> legalModifications = new ArrayList<>();
                                while (true) {
                                    totalAttempts++;
                                    int modifySetIteration = 0;

                                    for (Set<Integer> modifySet : list) {
                                        modifySetIteration++;
                                        String testLogFile = Constant.PROJ_LOG_BASE_PATH + "/" + _subject.getName() + "/Attempt_" + totalAttempts + "_mod" + modifySetIteration + "_" + _subject.getId() + ".tests";
                                        if (timer.timeout()) {
                                            return Status.TIMEOUT;
                                        }

                                        for (Integer index : modifySet) {
                                            modifications.get(index).apply(usableVars);
                                        }

                                        String replace = oneBuggyBlock.toSrcString().toString();
                                        if (replace.equals(currentBlockString)) {
                                            for (Integer index : modifySet) {
                                                modifications.get(index).restore();
                                            }
                                            continue;
                                        }
                                        if (haveTryPatches.contains(replace)) {
//								System.out.println("already try ...");
                                            for (Integer index : modifySet) {
                                                modifications.get(index).restore();
                                            }
                                            if (legalModifications != null) {
                                                for (Integer index : modifySet) {
                                                    legalModifications.add(modifications.get(index));
                                                }
                                            }
                                            continue;
                                        }

                                        if (!replace.isEmpty()) {
                                            System.out.println("======== PATCH BEGIN ========");
                                            System.out.println(replace.trim());
                                            System.out.println("-------- PATCH END --------");
                                        }

                                        haveTryPatches.add(replace);
                                        try {
                                            JavaFile.sourceReplace(file, source, range.getFirst(), range.getSecond(), replace);
                                        } catch (IOException e) {
                                            System.err.println("Failed to replace source code.");
                                            continue;
                                        }
                                        try {
                                            FileUtils.forceDelete(new File(binFile));
                                        } catch (IOException e) {
                                        }

                                        // validate correctness of patch
                                        switch (validate(logFile, oneBuggyBlock, range, file, loc.getFirst())) {
                                            case COMPILE_FAILED:
                                                System.out.println("Compilation failed, skipping tests");
//								haveTryPatches.remove(replace);
                                                break;
                                            case SUCCESS:
                                                // writeOriginalTestCaseStatus(testLogFile);

                                                String correctPatch = oneBuggyBlock.toSrcString().toString().replace("\\s*|\t|\r|\n", "");
                                                if (patches.contains(correctPatch)) {
                                                    continue;
                                                }
                                                patches.add(correctPatch);
                                                correct++;
                                                // for debug
                                                dumpPatch(logFile, "Similar code block : " + similar.getSecond(), file, new Pair<Integer, Integer>(0, 0), similar.getFirst().toSrcString().toString());
                                                dumpPatch(logFile, "Original source code", file, range, currentBlockString);
                                                dumpPatch(logFile, "Find a patch", file, range, oneBuggyBlock.toSrcString().toString());
                                                String target = Constant.HOME + "/patch/" + _subject.getName() + "/" + _subject.getId() + "/" + currentTry;

                                                File tarFile = new File(target);
                                                if (!tarFile.exists()) {
                                                    tarFile.mkdirs();
                                                }

                                                System.out.println("Successful patch found: " + testLogFile);

                                                File sourceFile = new File(file);
                                                FileUtils.copyFile(sourceFile, new File(target + "/" + totalAttempts + "_" + sourceFile.getName()));
                                                status = Status.SUCCESS;
                                                if (correct == Constant.PATCH_NUM) {
                                                    return Status.SUCCESS;
                                                }

                                                break; //remove passed revision
                                            case TEST_FAILED:

                                                // writeOriginalTestCaseStatus(testLogFile);
                                                System.out.println("Test suite failed: " + testLogFile);
                                                if (legalModifications != null) {
                                                    for (Integer index : modifySet) {
                                                        legalModifications.add(modifications.get(index));
                                                    }
                                                }
                                        }
                                        for (Integer index : modifySet) {
                                            modifications.get(index).restore();
                                        }
                                    }
                                    if (legalModifications == null) {
                                        break;
                                    }
                                    list = combineModification(legalModifications);
                                    modifications = legalModifications;
                                    legalModifications = null;
                                }
                            }
                        }
                    } else {
                        System.out.println(String.format("Skipping over correct file: %s", fileClass));
                    }
                }
            }
        }
        return status;
    }

    private void logMessage(String logFile, String message) {
        JavaFile.writeStringToFile(logFile, new Date(System.currentTimeMillis()).toString() + " " + message + "\n", true);
    }

    private void dumpPatch(String logFile, String message, String buggyFile, Pair<Integer, Integer> codeRange, String text) {
        StringBuffer stringBuffer = new StringBuffer();
        stringBuffer.append("\n----------------------------------------\n----------------------------------------\n");
        stringBuffer.append(message + " : [" + buggyFile + "=>" + codeRange.getFirst() + "," + codeRange.getSecond() + "]\n");
        stringBuffer.append(text);
        SimpleDateFormat simpleFormat = new SimpleDateFormat("yy/MM/dd HH:mm");
        stringBuffer.append("\nTime : " + simpleFormat.format(new Date()) + "\n");
        stringBuffer.append("----------------------------------------\n");
//		System.out.println(stringBuffer.toString());
        JavaFile.writeStringToFile(logFile, stringBuffer.toString(), true);
    }

    private void savePatch(String patch, String methodName, Pair<Integer, Integer> sourceRange) {
        File outputFile = new File(String.format("../simfix-output/%s-%d/patches/%d.patch", this._subject.getName(), this._subject.getId(), ++this.patchAttempts));
        outputFile.getParentFile().mkdirs();
        try (BufferedWriter bw = new BufferedWriter(new FileWriter(outputFile))) {
            bw.write("Method signature: " + methodName);
            bw.newLine();

            bw.write(String.format("Patched lines: %d - %d", sourceRange.getFirst(), sourceRange.getSecond()));
            bw.newLine();

            bw.write("------------");
            bw.newLine();

            bw.write(patch);
            bw.newLine();
        } catch (IOException ex) {
            System.err.println(ex.getMessage());
        }
    }

    private List<Modification> removeDuplicateModifications(List<Modification> modifications) {
        //remove duplicate modifications
        List<Modification> unique = new LinkedList<>();
        for (Modification modification : modifications) {
            boolean exist = false;
            for (Modification u : unique) {
                if (u.getRevisionTypeID() == modification.getRevisionTypeID()
                        && u.getSourceID() == modification.getSourceID()
                        && u.getTargetString().equals(modification.getTargetString())
                        && u.getSrcNode().toSrcString().toString().equals(modification.getSrcNode())) {
                    exist = true;
                    break;
                }
            }
            if (!exist) {
                unique.add(modification);
            }
        }
        return unique;
    }

    private List<Set<Integer>> consistentModification(List<Modification> modifications) {
        List<Set<Integer>> result = new LinkedList<>();
        String regex = "[A-Za-z_][0-9A-Za-z_.]*";
        Pattern pattern = Pattern.compile(regex);
        for (int i = 0; i < modifications.size(); i++) {
            Modification modification = modifications.get(i);
            if (modification instanceof Revision) {
                Set<Integer> consistant = new HashSet<>();
                consistant.add(i);
                for (int j = i + 1; j < modifications.size(); j++) {
                    try {
                        Modification other = modifications.get(j);
                        if (other instanceof Revision) {
                            if (modification.compatible(other) && modification.getTargetString().equals(other.getTargetString())) {
                                ASTNode node = JavaFile.genAST(modification.getTargetString(), ASTParser.K_EXPRESSION);
                                if (node instanceof Name || node instanceof FieldAccess || pattern.matcher(modification.getTargetString()).matches()) {
                                    consistant.add(j);
                                }
                            }
                        }
                    } catch (Exception e) {
                        System.err.println(String.format("Error during repair process found: %s: ", e.getMessage()));
                    }
                }

                if (consistant.size() > 1) {
                    result.add(consistant);
                }
            }
        }

        return result;
    }

    private List<Set<Integer>> combineModification(List<Modification> modifications) {
        List<Set<Integer>> list = new ArrayList<>();
        int length = modifications.size();
        if (length == 0) {
            return list;
        }
        int[][] incompatibleMap = new int[length][length];
        for (int i = 0; i < length; i++) {
            for (int j = i; j < length; j++) {
                if (i == j) {
                    incompatibleMap[i][j] = 1;
                } else if (modifications.get(i).compatible(modifications.get(j))) {
                    incompatibleMap[i][j] = 0;
                    incompatibleMap[j][i] = 0;
                } else {
                    incompatibleMap[i][j] = 1;
                    incompatibleMap[i][j] = 1;
                }
            }
        }
        List<Set<Integer>> baseSet = new ArrayList<>();
        for (int i = 0; i < modifications.size(); i++) {
            Set<Integer> set = new HashSet<>();
            set.add(i);
            baseSet.add(set);
        }

//		List<Set<Integer>> expanded = expand(incompatibleMap, baseSet, 2, 3);
//		for(Set<Integer> set : expanded){
//			Set<Modification> combinedModification = new HashSet<>();
//			for(Integer integer : set){
//				combinedModification.add(modifications.get(integer));
//			}
//			list.add(combinedModification);
//		}
        list.addAll(expand(incompatibleMap, baseSet, 2, 4));

        return list;
    }

    private List<Set<Integer>> expand(int[][] incompatibleTabe, List<Set<Integer>> baseSet, int currentSize, int upperbound) {
        List<Set<Integer>> rslt = new LinkedList<>();
        if (currentSize > upperbound) {
            return rslt;
        }
        while (baseSet.size() > 1000) {
            baseSet.remove(baseSet.size() - 1);
        }
        int length = incompatibleTabe.length;
        for (Set<Integer> base : baseSet) {
            int minIndex = 0;
            for (Integer integer : base) {
                if (integer > minIndex) {
                    minIndex = integer;
                }
            }

            for (minIndex++; minIndex < length; minIndex++) {
                boolean canExd = true;
                for (Integer integer : base) {
                    if (incompatibleTabe[minIndex][integer] == 1) {
                        canExd = false;
                        break;
                    }
                }
                if (canExd) {
                    Set<Integer> expanded = new HashSet<>(base);
                    expanded.add(minIndex);
                    rslt.add(expanded);
                }
            }
        }

        if (rslt.size() > 0) {
            rslt.addAll(expand(incompatibleTabe, rslt, currentSize + 1, upperbound));
        }

        return rslt;
    }

    private ValidateStatus validate(String logFile, CodeBlock buggyBlock, Pair<Integer, Integer> sourceRange, String file, String file2) {
//        System.out.println("start:" + buggyBlock.getStartLine());
//        System.out.println("end:" + buggyBlock.getEndLine());
//        System.out.println("max:" + buggyBlock.getMaxLines());
//        System.out.println("modified srcStart=" + sourceRange.getFirst());
//        System.out.println("modified srcEnd=" + sourceRange.getSecond());
//        System.out.println("modified file=" + file);

        String methodName = "";
        Map<String, Double> newMap = new TreeMap();

        try {
            methodName = profl.getMethodCoverage().getMethodFromPackageNumber(file2, sourceRange.getFirst());
            System.out.println(String.format("Modified method %s from %d to %d", methodName, sourceRange.getFirst(), sourceRange.getFirst()));
            newMap.put(methodName, profl.getGeneralMethodSusValues().get(methodName));
        } catch (Exception e) {
            System.out.println("Could not find method signature for " + file2 + " at line " + sourceRange.getFirst());
            System.out.println(e.getMessage());
        }

        if (!Runner.compileSubject(_subject)) {
            System.out.println("Build failed !");
            return ValidateStatus.COMPILE_FAILED;
        }

        Set<String> failPass = new TreeSet();
        Set<String> failFail = new TreeSet();
        Set<String> passFail = new TreeSet();
        Set<String> passPass = new TreeSet();

        System.out.println("-------- PROCESSING TESTS BEGIN --------");

        ValidateStatus stop = ValidateStatus.SUCCESS; // risky 

        // validate patch using originally failed test cases
        for (String testcase : _failedTestCases) {

            String[] testinfo = testcase.split("::");
            if (!Runner.testSingleTest(_subject, testinfo[0], testinfo[1])) {
                failFail.add(testcase);
                // writeNewFailFailTestCaseStatus(testcase, testLogName); // return after for loop if complete list of fail test cases is needed

                stop = ValidateStatus.TEST_FAILED;
            } else {
                failPass.add(testcase);
                // writeNewFailPassTestCaseStatus(testcase, testLogName);
            }
        }

        dumpPatch(logFile, "Pass Single Test", "", new Pair<Integer, Integer>(0, 0), buggyBlock.toSrcString().toString());

        List<String> validationTestResults = Runner.runTestSuite(_subject);

        for (String failed : validationTestResults) {
            if (_failedTestCases.contains(failed)) {
                failFail.add(failed);
            } else {
                passFail.add(failed);
            }
        }

        for (String testcase : _failedTestCases) {
            if (!validationTestResults.contains(testcase)) {
                failPass.add(testcase);
            }
        }

        boolean successfulTestSuite = validationTestResults.isEmpty();
        boolean failPassTestsExist = !failPass.isEmpty();
        boolean passFailTestsExist = (failFail.isEmpty() && !successfulTestSuite);

        if (!newMap.isEmpty()) {

            savePatch(buggyBlock.toSrcString().toString(), methodName, sourceRange);
            System.out.println(String.format("--- Information for Patch %d --- [START]", this.patchAttempts));
            if (!failPass.isEmpty() && passFail.isEmpty()) {
                if (failFail.isEmpty()) {
                    System.out.println("Full CleanFix detected");
                    profl.addCategoryEntry(DefaultPatchCategories.CLEAN_FIX_FULL, newMap);
                } else {
                    System.out.println("Partial CleanFix detected");
                    profl.addCategoryEntry(DefaultPatchCategories.CLEAN_FIX_PARTIAL, newMap);
                }
            } else if (!failPass.isEmpty() && !passFail.isEmpty()) {
                if (failFail.isEmpty()) {
                    System.out.println("Full NoisyFix detected");
                    profl.addCategoryEntry(DefaultPatchCategories.NOISY_FIX_FULL, newMap);
                } else {
                    System.out.println("Partial NoisyFix detected");
                    profl.addCategoryEntry(DefaultPatchCategories.NOISY_FIX_PARTIAL, newMap);
                }

            } else if (failPass.isEmpty() && passFail.isEmpty()) {
                System.out.println("NoneFix detected");
                profl.addCategoryEntry(DefaultPatchCategories.NONE_FIX, newMap);
            } else {
                System.out.println("NegFix detected!");
                profl.addCategoryEntry(DefaultPatchCategories.NEG_FIX, newMap);
            }

            saveProflData();
            System.out.println(String.format("--- Information for Patch %d --- [END]", this.patchAttempts));
        }

        System.out.println("-------- PROCESSING TESTS END --------");

        if (failFail.isEmpty() && passFail.isEmpty()) {
            return ValidateStatus.TEST_FAILED;
        }

        return stop;
    }

    private void saveProflData() {
        File genOutputFile = new File(String.format("../simfix-output/%s-%d/generalSusInfo.profl", this._subject.getName(), this._subject.getId()));
        File susOutputFile = new File(String.format("../simfix-output/%s-%d/aggregatedSusInfo.profl", this._subject.getName(), this._subject.getId()));
        File catOutputFile = new File(String.format("../simfix-output/%s-%d/category_information.profl", this._subject.getName(), this._subject.getId()));

        genOutputFile.getParentFile().mkdirs();
        susOutputFile.getParentFile().mkdirs();
        catOutputFile.getParentFile().mkdirs();

        try (BufferedWriter bw = new BufferedWriter(new FileWriter(genOutputFile))) {
            System.out.println("Saving information to " + genOutputFile.getAbsolutePath());
            for (String s : profl.outputSbflSus()) {
                bw.write(s);
                bw.newLine();
            }
        } catch (Exception e) {
            System.out.println(e.getMessage());
        }

        try (BufferedWriter bw = new BufferedWriter(new FileWriter(susOutputFile))) {
            System.out.println("Saving information to " + susOutputFile.getAbsolutePath());
            for (String s : profl.outputProflResults()) {
                bw.write(s);
                bw.newLine();
            }
        } catch (Exception e) {
            System.out.println(e.getMessage());
        }

        try (BufferedWriter bw = new BufferedWriter(new FileWriter(catOutputFile))) {
            System.out.println("Saving information to " + catOutputFile.getAbsolutePath());
            for (String s : profl.outputProflCatInfo()) {
                bw.write(s);
                bw.newLine();
            }
        } catch (Exception e) {
            System.out.println(e.getMessage());
        }
    }

    private void writeNewFailFailTestCaseStatus(String testcase, String testLogName) {
        System.out.println(String.format("[FAIL->FAIL test case] %s", testcase));
        JavaFile.writeStringToFile(testLogName, String.format("[FAIL->FAIL test case] %s%n", testcase), true);
    }

    private void writeNewFailPassTestCaseStatus(String testcase, String testLogName) {
        System.out.println(String.format("[FAIL->PASS test case] %s", testcase));
        JavaFile.writeStringToFile(testLogName, String.format("[FAIL->PASS test case] %s%n", testcase), true);
    }

    // Do not have explicit access to passing test suite
    private void writeNewPassFailTestCaseStatus(String testcase, String testLogName) {
        System.out.println(String.format("[PASS->FAIL test case] %s", testcase));
        JavaFile.writeStringToFile(testLogName, String.format("[PASS->FAIL test case] %s%n", testcase), true);
    }

    private void writeNewPassPassTestCaseStatus(String testcase, String testLogName) {
        System.out.println(String.format("[PASS->PASS test case] %s", testcase));
        JavaFile.writeStringToFile(testLogName, String.format("[PASS->PASS test case] %s%n", testcase), true);
    }

    private void writeOriginalTestCaseStatus(String testLogName) {

        JavaFile.writeStringToFile(testLogName, String.format("Total number of test cases: %d%n", _localization.getFailedTestCases().size() + _localization.getPassedTestCases().size()), true);

        for (String s : this._localization.getFailedTestCases()) {
            JavaFile.writeStringToFile(testLogName, String.format("[Originally FAILING test case] %s%n", s), true);
        }

        for (String s : this._localization.getPassedTestCases()) {
            JavaFile.writeStringToFile(testLogName, String.format("[Originally PASSING test case] %s%n", s), true);
        }
    }

    private enum ValidateStatus {
        COMPILE_FAILED,
        TEST_FAILED,
        SUCCESS
    }

}
