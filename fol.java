
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Objects;

/**
 *
 * @author pbharat
 */
public class fol {

    public static String[] queries;
    public static boolean[] result;
    public static ArrayList<String> kb = new ArrayList<>();
    public static HashMap<Predicate, Integer> predicates = new HashMap<>();  // how many unique predicates and their indexes in kb sentences
    public static ArrayList<Predicate> predicateList = new ArrayList<>();
    public static ArrayList<HashSet<Integer>> kbSentences = new ArrayList<>(); // sentences corresponds to 
    public static Integer kbLastIndex = 0;
    public static Integer limit = 15000;

    public static void main(String[] args) {
        readInput();
        parseKbSentences();
        for (Integer i = 0; i < queries.length; i++) {
            result[i] = resolve(i);
        }
        writeOutput();
    }

    public static void readInput() {
        String path = "input.txt";
        try (FileReader fileReader = new FileReader(path); BufferedReader bufferedReader = new BufferedReader(fileReader)) {
            String line = null;
            Integer totalQueries = 0, totalClauses = 0;
            if (null != (line = bufferedReader.readLine())) {
                totalQueries = Integer.valueOf(line);
            }
            result = new boolean[totalQueries];
            queries = new String[totalQueries];
            Arrays.fill(result, Boolean.FALSE);
            for (int i = 0; i < totalQueries && null != (line = bufferedReader.readLine()); i++) {
                queries[i] = line;
            }
            if (null != (line = bufferedReader.readLine())) {
                totalClauses = Integer.valueOf(line);
            }
            kbLastIndex = totalClauses - 1;
            limit = totalClauses * totalClauses >= 100 * totalClauses ? totalClauses * totalClauses : 100 * totalClauses;
            for (int i = 0; i < totalClauses && null != (line = bufferedReader.readLine()); i++) {
                kb.add(line);
            }
        } catch (FileNotFoundException e) {
        } catch (IOException e) {
        }
    }

    public static void writeOutput() {
        String path = "output.txt";
        try (FileWriter fileWriter = new FileWriter(path); BufferedWriter bufferedWriter = new BufferedWriter(fileWriter)) {
            for (Integer i = 0; i < result.length; i++) {
                String output = result[i] ? "TRUE" : "FALSE";
                bufferedWriter.write(output);
                bufferedWriter.newLine();
            }
        } catch (FileNotFoundException e) {
        } catch (IOException e) {
        }
    }

    public static HashMap<String, Integer> uniqueVariablesInSentence(String clause) {
        String[] terms = clause.split("\\|");
        HashMap<String, Integer> frequency = new HashMap<>();
        for (String term : terms) {
            Integer start = term.indexOf("(");
            Integer end = term.indexOf(")");
            String[] arguments = term.substring(start + 1, end).split(",");
            for (String a : arguments) {
                if (isVariable(a)) {
                    if (!frequency.containsKey(a)) {
                        Integer count = frequency.size() + 1;
                        frequency.put(a, count);
                    }
                }
            }
        }
        return frequency;
    }

    public static HashSet<Integer> removeRedundancy(HashSet<Integer> clause, HashMap<Predicate, Integer> parentPredicates,
            ArrayList<Predicate> parentPredicateList) {
        HashMap<String, Integer> unique = new HashMap<>();
        ArrayList<Integer> sentence = new ArrayList<>(clause);
        for (Integer i : sentence) {
            Predicate p = parentPredicateList.get(i);
            String[] args = p.getArguments();
            for (String a : args) {
                if (isVariable(a)) {
                    if (!unique.containsKey(a)) {
                        Integer count = unique.size() + 1;
                        unique.put(a, count);
                    }
                }
            }
        }
        HashSet<Integer> newClause = new HashSet<>();
        for (Integer i : sentence) {
            Predicate p = parentPredicateList.get(i);
            Predicate term = new Predicate(p.getName(), p.isNegated(), p.getArguments(), unique);
            if (parentPredicateList.contains(term)) {
                newClause.add(parentPredicates.get(term));
            } else {
                Integer count = parentPredicateList.size();
                parentPredicates.put(term, count);
                parentPredicateList.add(term);
                newClause.add(count);
            }
        }

        return newClause;
    }

    public static void parseKbSentences() {
        if (0 == kb.size()) {
            return;
        }
        for (String sentence : kb) {
            sentence = sentence.replaceAll("\\s", "");
            HashMap<String, Integer> frequency = uniqueVariablesInSentence(sentence);
            String[] terms = sentence.split("\\|");
            HashSet<Integer> indexes = new HashSet<>();
            for (String term : terms) {
                Integer start = term.indexOf("(");
                Integer end = term.indexOf(")");
                Predicate predicate = new Predicate(term, start, end, frequency);
                if (!predicates.containsKey(predicate)) {
                    Integer i = predicates.size();
                    predicates.put(predicate, i);
                    indexes.add(i);
                    predicateList.add(predicate);
                } else {
                    indexes.add(predicates.get(predicate));
                }
            }
            kbSentences.add(indexes);
        }
    }

    public static HashSet<Integer> removeTautology(HashSet<Integer> clause, HashMap<Predicate, Integer> parentPredicates,
            ArrayList<Predicate> parentPredicateList) {
        ArrayList<Integer> sentence = new ArrayList<>(clause);
        HashSet<Integer> newClause = new HashSet<>(clause);
        for (Integer i = 0; i < sentence.size() - 1; i++) {
            Predicate p1 = parentPredicateList.get(sentence.get(i));
            for (Integer j = i + 1; j < sentence.size(); j++) {
                Predicate p2 = parentPredicateList.get(sentence.get(j));
                if (p1.isNegatedPredicate(p2)) {
                    newClause.remove(sentence.get(i));
                    newClause.remove(sentence.get(j));
                }
            }
        }
        return newClause;
    }

    public static boolean isNegatedPredicates(Predicate p1, Predicate p2) {
        if (null == p1 || p2 == null) {
            return false;
        }
        if (!Objects.equals(p1.getName(), p2.getName())) {
            return false;
        }
        if (p1.isNegated() == p2.isNegated()) {
            return false;
        }
        if (p1.getArguments().length != p2.getArguments().length) {
            return false;
        }
        String[] args1 = p1.getArguments();
        String[] args2 = p2.getArguments();
        for (Integer i = 0; i < args1.length; i++) {
            if (isVariable(args1[i]) && isVariable(args2[i])) {
                return true;
            } else if (!isVariable(args1[i]) && !isVariable(args2[i])) {
                if (args1[1].equals(args2[i])) {
                    return true;
                } else {
                    return false;
                }
            } else {
                return false;
            }
        }
        return true;
    }

    public static String findPredicateNameWithNegation(Predicate p) {
        if (null == p) {
            return null;
        }
        StringBuilder name = new StringBuilder();
        if (p.isNegated()) {
            name.append("~");
        }
        name.append(p.getName());
        return name.toString();
    }

    public static String findNegatedPredicateName(Predicate p) {
        if (null == p) {
            return null;
        }
        StringBuilder name = new StringBuilder();
        if (!p.isNegated()) {
            name.append("~");
        }
        name.append(p.getName());
        return name.toString();
    }

    public static boolean resolve(Integer askIndex) {
        ArrayList<HashSet<Integer>> facts = new ArrayList<>(kbSentences);     //copy of KB
        HashMap<Predicate, Integer> newPredicates = new HashMap<>(predicates);
        ArrayList<Predicate> newPredicateList = new ArrayList<>(predicateList);
        Integer pCount = newPredicates.size();

        String query = queries[askIndex];
        query = query.replaceAll("\\s", "");
        Integer start = query.indexOf("(");
        Integer end = query.indexOf(")");
        if (-1 == start || -1 == end || start >= end) {
            return false;
        }
        HashMap<String, Integer> frequency = uniqueVariablesInSentence(query);
        Predicate ask = new Predicate(query, start, end, frequency);
        ask.setNegated(!ask.isNegated());
        HashSet<Integer> newFact = new HashSet<>();
        if (!newPredicates.containsKey(ask)) {
            newPredicates.put(ask, pCount);
            newPredicateList.add(ask);
            newFact.add(pCount);
        } else {
            newFact.add(newPredicates.get(ask));
        }
        facts.add(newFact);             //negation of the query added to the KB
        return resolution(facts, newPredicates, newPredicateList);
    }

    public static boolean resolution(ArrayList<HashSet<Integer>> parentKb, HashMap<Predicate, Integer> parentPredicates,
            ArrayList<Predicate> parentPredicateList) {

        HashSet<HashSet<Integer>> newClauses = new HashSet<>();
        do {
            for (Integer a = 0; a < parentKb.size() - 1; a++) {
                HashSet<Integer> clause1 = parentKb.get(a);
                for (Integer b = a + 1; b < parentKb.size(); b++) {
                    if (!(a <= kbLastIndex && b <= kbLastIndex)) {
                        HashSet<Integer> clause2 = parentKb.get(b);
                        HashSet<HashSet<Integer>> resolvents = twoClausesResolution(clause1, clause2, a, b, parentPredicateList, parentPredicates);
                        HashSet<HashSet<Integer>> newResolvents = new HashSet<>();
                        for (HashSet<Integer> r : resolvents) {
                            r = removeRedundancy(r, parentPredicates, parentPredicateList);
                            r = removeTautology(r, parentPredicates, parentPredicateList);
                            newResolvents.add(r);
                        }
                        if (newResolvents.contains(new HashSet<>())) {
                            return true;
                        }
                        newClauses.addAll(newResolvents);
                    }
                }
            }
            HashSet<HashSet<Integer>> clauses = new HashSet<>(parentKb);
            if (clauses.containsAll(newClauses)) {
                return false;
            }
            newClauses.removeAll(clauses);
            for (HashSet<Integer> r : newClauses) {
                parentKb.add(r);
            }
            if (parentKb.size() > limit) {
//                System.out.println("Limit : " + limit + " size: " + parentKb.size());
                return false;
            }
        } while (true);
    }

    public static HashSet<HashSet<Integer>> twoClausesResolution(HashSet<Integer> c1, HashSet<Integer> c2, Integer c1Index,
            Integer c2Index, ArrayList<Predicate> parentPredicateList, HashMap<Predicate, Integer> parentPredicates) {
        HashSet<HashSet<Integer>> resolvents = new HashSet<>();
        for (Integer pIndex : c1) {
            Predicate p1 = parentPredicateList.get(pIndex);
            for (Integer j : c2) {
                Predicate p2 = parentPredicateList.get(j);
                if (p2.isNegated() != p1.isNegated() && p2.getName().equals(p1.getName())) {
                    Substitutions s = new Substitutions();
                    s = unify(p1, p2, s);
                    if (null != s) {
                        HashSet<Integer> resolvent = pruneClause(c1, c2, s, pIndex, j, parentPredicateList, parentPredicates);
                        resolvents.add(resolvent);
                    }
                }
            }
        }
        return resolvents;
    }

    public static HashSet<Integer> pruneClause(HashSet<Integer> c1, HashSet<Integer> c2, Substitutions s, Integer r1, Integer r2,
            ArrayList<Predicate> parentPredicateList, HashMap<Predicate, Integer> parentPredicates) {
        HashSet<Integer> clause = new HashSet<>();
        for (Integer i : c1) {
            if (i != r1) {
                Predicate p = predicateReplace(parentPredicateList.get(i), s);
                if (null != p) {
                    if (parentPredicateList.contains(p)) {
                        clause.add(parentPredicates.get(p));
                    } else {
                        Integer count = parentPredicateList.size();
                        parentPredicates.put(p, count);
                        parentPredicateList.add(p);
                        clause.add(count);
                    }
                }
            }
        }
        for (Integer i : c2) {
            if (i != r2) {
                Predicate p = predicateReplace(parentPredicateList.get(i), s);
                if (null != p) {
                    if (parentPredicateList.contains(p)) {
                        clause.add(parentPredicates.get(p));
                    } else {
                        Integer count = parentPredicateList.size();
                        parentPredicates.put(p, count);
                        parentPredicateList.add(p);
                        clause.add(count);
                    }
                }
            }

        }
        return clause;
    }

    public static HashSet<Integer> unionOfSets(HashSet<Integer> s1, HashSet<Integer> s2) {
        HashSet<Integer> union = new HashSet<>(s1);
        union.addAll(s2);
        return union;
    }

    public static boolean isVariable(String argument) {
        if (argument.length() == 1 && argument.charAt(0) >= 97 && argument.charAt(0) < 123) {
            return true;
        }
        return argument.contains("VAR");
    }

    public static Substitutions unify(Predicate one, Predicate another, Substitutions s) {
        if (null == one || null == another) {
            return null;
        }
        if (one.getArguments().length != another.getArguments().length) {
            return null;
        }
        if (!one.getName().equals(another.getName())) {
            return null;
        }
        if (one.isNegated() == another.isNegated()) {
            return null;
        }
        if (one.isNegatedPredicate(another)) { // special case for matchings like A(x) and ~A(x)
            return s;
        }
        String[] oneArguments = one.getArguments();
        String[] anotherArguments = another.getArguments();
        Substitutions sNew = new Substitutions(s);
        for (Integer i = 0; i < one.getArguments().length; i++) {
            sNew = variableUnification(oneArguments[i], anotherArguments[i], sNew);
            if (null == sNew) {
                return null;
            }
        }
        return sNew;
    }

    /**
     *
     * @param constant1 it must be a constant
     * @param constant2 can be a constant or a variable
     */
    public static Substitutions constantUnification(String constant1, String constant2, Substitutions s) {
        if (constant1.equals(constant2)) {
            return s;
        }
        if (isVariable(constant2)) {
            return variableUnification(constant2, constant1, s);
        }
        return null;
    }

    public static Substitutions variableUnification(String variable, String value, Substitutions s) {
        if (variable.equals(value)) {
            return s;
        }
        if (!isVariable(variable)) {
            return constantUnification(variable, value, s);
        }
        if (s.isBound(variable)) {
            return variableUnification(s.getValue(variable), value, s);
        }
        Substitutions sNew = new Substitutions(s);
        sNew.add(variable, value);
        return sNew;
    }

    public static String variableReplace(String variable, Substitutions s) {
        if (!isVariable(variable)) {
            return variable;
        }
        if (s.isBound(variable)) {
//            return variableReplace(s.getValue(variable), s);
            return s.getValue(variable);
        }
        return variable;
    }

    public static Predicate predicateReplace(Predicate p, Substitutions s) {
        if (null == p) {
            return null;
        }
        Predicate predicate = new Predicate();
        predicate.setName(p.getName());
        predicate.setNegated(p.isNegated());
        String[] newArguments = new String[p.getArguments().length];
        String[] arguments = p.getArguments();
        for (Integer i = 0; i < arguments.length; i++) {
            newArguments[i] = variableReplace(arguments[i], s);
        }
        predicate.setArguments(newArguments);
        return predicate;
    }

}

class Predicate implements Comparable<Predicate> {

    private String name;
    private String[] arguments;
    private boolean negated;

    public Predicate() {
    }

    public Predicate(String term, Integer start, Integer end, HashMap<String, Integer> frequency) {
        if ('~' == term.charAt(0)) {
            this.negated = Boolean.TRUE;
        } else {
            this.negated = Boolean.FALSE;
        }
        Integer index = 0;
        if (this.negated) {
            index = 1;
        }
        this.name = term.substring(index, start);
        this.arguments = modifyArguments(term.substring(start + 1, end).split(","), frequency);
    }

    public Predicate(String name, boolean negated, String[] args, HashMap<String, Integer> unique) {
        this.negated = negated;
        this.name = name;
        this.arguments = modifyArguments(args, unique);
    }

    public Predicate(boolean negated, String name, String... params) {
        this.name = name;
        this.arguments = params;
        this.negated = negated;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public String[] getArguments() {
        return arguments;
    }

    public void setArguments(String[] arguments) {
        this.arguments = arguments;
    }

    public boolean isNegated() {
        return negated;
    }

    public void setNegated(boolean negated) {
        this.negated = negated;
    }

    @Override
    public String toString() {
        StringBuilder s = new StringBuilder();
        if (negated) {
            s.append("~");
        }
        s.append(name);
        s.append("(");
        Integer count = 0;
        Integer lastIndex = arguments.length - 1;
        for (String arg : arguments) {
            s.append(arg);
            if (count != lastIndex) {
                s.append(",");
            }
            count++;
        }
        s.append(")");
        return s.toString();
    }

    @Override
    public int hashCode() {
        int hash = 3;
        hash = 59 * hash + Objects.hashCode(this.name);
        hash = 59 * hash + Arrays.deepHashCode(this.arguments);
        hash = 59 * hash + (this.negated ? 1 : 0);
        return hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final Predicate other = (Predicate) obj;
        if (this.negated != other.negated) {
            return false;
        }
        if (!Objects.equals(this.name, other.name)) {
            return false;
        }
        if (!Arrays.deepEquals(this.arguments, other.arguments)) {
            return false;
        }
        return true;
    }

    @Override
    public int compareTo(Predicate o) {
        Integer result = 0;
        if (this.equals(o)) {
            result = 1;
        }
        return result;
    }

    public boolean isNegatedPredicate(Predicate obj) {
        if (obj == null) {
            return false;
        }
        if (!Objects.equals(this.name, obj.getName())) {
            return false;
        }
        if (!Arrays.deepEquals(this.arguments, obj.getArguments())) {
            return false;
        }
        if (this.negated == obj.isNegated()) {
            return false;
        }
        return true;
    }

    public boolean isVariable(String argument) {
        if (argument.length() == 1 && argument.charAt(0) >= 97 && argument.charAt(0) < 123) {
            return true;
        }
        return argument.contains("VAR");
    }

    public String[] modifyArguments(String[] args, HashMap<String, Integer> frequency) {
        Integer count = args.length;
        String[] modified = new String[count];
        for (Integer i = 0; i < count; i++) {
            if (frequency.containsKey(args[i])) {
                StringBuilder s = new StringBuilder();
                s.append("VAR");
                s.append(String.valueOf(frequency.get(args[i])));
                modified[i] = s.toString();
            } else {
                modified[i] = args[i];
            }
        }
        return modified;
    }

}

class Substitutions {

    private HashMap<String, String> bindings = new HashMap<>();

    public Substitutions() {
    }

    public Substitutions(Substitutions s) {
        this.bindings = new HashMap<>(s.getBindings());
    }

    public void clear() {
        this.bindings.clear();
    }

    public void add(String variable, String value) {
        this.bindings.put(variable, value);
    }

    public String getValue(String variable) {
        return this.bindings.get(variable);
    }

    public boolean isBound(String variable) {
        return this.bindings.containsKey(variable);
    }

    public HashMap<String, String> getBindings() {
        return bindings;
    }

    public void setBindings(HashMap<String, String> bindings) {
        this.bindings = bindings;
    }

    @Override
    public String toString() {
        return "Substitutions{" + "bindings=" + bindings + '}';
    }

}
