# # # ---------- CORE DATA STRUCTURES ----------
import re
# from typing import List, Set


class Term: pass

class Variable(Term):
    def __init__(self, name): self.name = name
    def __hash__(self): return hash(self.name)
    def __eq__(self, other): return isinstance(other, Variable) and self.name == other.name
    def __repr__(self): return self.name

class Constant(Term):
    def __init__(self, name): self.name = name
    def __hash__(self): return hash(self.name)
    def __eq__(self, other): return isinstance(other, Constant) and self.name == other.name
    def __repr__(self): return self.name

class Function(Term):
    def __init__(self, name, args):
        self.name, self.args = name, tuple(args)
    def __hash__(self): return hash((self.name, self.args))
    def __eq__(self, other): return isinstance(other, Function) and self.name == other.name and self.args == other.args
    def __repr__(self): return f"{self.name}({', '.join(map(repr, self.args))})"

class Predicate:
    def __init__(self, name, args, negated=False):
        self.name, self.args, self.negated = name, tuple(args), negated
    def __hash__(self): return hash((self.name, self.args, self.negated))
    def __eq__(self, other): 
        return isinstance(other, Predicate) and self.name == other.name and self.args == other.args and self.negated == other.negated
    def __repr__(self): return f"{'¬' if self.negated else ''}{self.name}({', '.join(map(repr, self.args))})"

class Clause:
    _id_counter = 0
    def __init__(self, literals, parents=None):
        self.literals = frozenset(literals)
        self.id = Clause._id_counter
        Clause._id_counter += 1
        self.parents = parents
    @staticmethod
    def reset(): Clause._id_counter = 0
    def is_empty(self): return len(self.literals) == 0
    def __repr__(self):
        if self.is_empty(): return "□"
        return f"C{self.id}: " + " ∨ ".join(map(repr, sorted(list(self.literals), key=lambda x: x.name)))
    def __hash__(self): return hash(self.literals)
    def __eq__(self, other): return isinstance(other, Clause) and self.literals == other.literals

class TheoremProver:
    def __init__(self, include_set_axioms=True):
        # Axioms are now built-in with protected variable names (ax_v1, etc.)
        self.base_axioms = [
            # 1. Empty Set: Nothing is in the EmptySet
            "∀ax_v1 ¬In(ax_v1, EmptySet)",

            # 2. Universal Set: Everything is in the UniversalSet
            "∀ax_v1 In(ax_v1, UniversalSet)",

            # 3. Intersection: x in (A ∩ B) iff (x in A AND x in B)
            "∀ax_v1 ∀ax_a ∀ax_b (In(ax_v1, Intersect(ax_a, ax_b)) ↔ (In(ax_v1, ax_a) ∧ In(ax_v1, ax_b)))",

            # 4. Union: x in (A ∪ B) iff (x in A OR x in B)
            "∀ax_v1 ∀ax_a ∀ax_b (In(ax_v1, Union(ax_a, ax_b)) ↔ (In(ax_v1, ax_a) ∨ In(ax_v1, ax_b)))",

            # 5. Subset: A is subset of B iff (for all x, x in A implies x in B)
            "∀ax_a ∀ax_b (Subset(ax_a, ax_b) ↔ ∀ax_v1 (In(ax_v1, ax_a) → In(ax_v1, ax_b)))",

            # 6. Difference: x in (A \ B) iff (x in A AND x not in B)
            "∀ax_v1 ∀ax_a ∀ax_b (In(ax_v1, Difference(ax_a, ax_b)) ↔ (In(ax_v1, ax_a) ∧ ¬In(ax_v1, ax_b)))",

            # 7. Equality (Extensionality): A equals B iff (A subset B AND B subset A)
            "∀ax_a ∀ax_b (Equals(ax_a, ax_b) ↔ (Subset(ax_a, ax_b) ∧ Subset(ax_b, ax_a)))"
        ] if include_set_axioms else []
        self.var_count = 0
        self.sk_count = 0

    def _tokenize(self, s):
        # Added support for lowercase keywords from your screenshots
        s = s.replace('forall', ' FORALL ').replace('exists', ' EXISTS ')
        s = s.replace('not', ' NOT ').replace('and', ' AND ')
        s = s.replace('or', ' OR ').replace('implies', ' IMPLIES ').replace('iff', ' IFF ')
        
        s = s.replace('forall', ' FORALL ').replace('iff', ' IFF ').replace('implies', ' IMPLIES ')

        # Keep existing symbol support
        s = s.replace('∀', ' FORALL ').replace('∃', ' EXISTS ').replace('¬', ' NOT ')
        s = s.replace('∧', ' AND ').replace('∨', ' OR ').replace('→', ' IMPLIES ').replace('↔', ' IFF ')
        s = s.replace('~', ' NOT ').replace('&', ' AND ').replace('|', ' OR ').replace('->', ' IMPLIES ').replace('<->', ' IFF ')
        
        s = s.replace('.', ' ')
        for p in '(),': s = s.replace(p, f' {p} ')
        return [t for t in s.split() if t]

    def _parse(self, tokens):
        pos = 0
        def peek(): return tokens[pos] if pos < len(tokens) else None
        def consume(): nonlocal pos; pos += 1; return tokens[pos-1]
        def parse_formula(): return parse_iff()
        def parse_iff():
            node = parse_implies()
            while peek() == 'IFF': 
                consume()
                # Wrap the current node and the next one in an IFF tuple
                node = ('IFF', [node, parse_implies()])
            return node # If no IFF is found, it returns the node from parse_implies

        def parse_implies():
            node = parse_or()
            while peek() == 'IMPLIES': 
                consume()
                node = ('IMPLIES', [node, parse_or()])
            return node

        def parse_or():
            node = parse_and()
            while peek() == 'OR': consume(); node = ('OR', [node, parse_and()])
            return node
        def parse_and():
            node = parse_unary()
            while peek() == 'AND': consume(); node = ('AND', [node, parse_unary()])
            return node
        
        def parse_unary():
            t = peek()
            if t == 'NOT':
                consume()
                return ('NOT', parse_unary()) # Ensure 'return' is here
            
            if t in ('FORALL', 'EXISTS'):
                q = consume()
                v = consume()
                # Some versions of this axiom have a '.' or '(' after the variable
                if peek() == '.': consume() 
                return (q, v, parse_unary()) # Ensure 'return' is here
            
            if t == '(':
                consume()
                res = parse_formula()
                consume() # pop ')'
                return res
            
            return parse_pred()

        def parse_pred():
            name = consume()
            if peek() == '(':
                consume(); args = []
                while True:
                    args.append(parse_term())
                    if peek() == ',': consume()
                    else: break
                consume(); return ('PRED', name, args)
            return ('PRED', name, [])
        def parse_term():
            name = consume()
            if peek() == '(':
                consume(); args = []
                while True:
                    args.append(parse_term())
                    if peek() == ',': consume()
                    else: break
                consume(); return ('FUNC', name, args)
            return ('VAR' if (name[0].islower() or name.startswith('ax_v')) else 'CONST', name)
        return parse_formula()

    def _to_ast(self, node, bounds):
        if node is None: return None # Safety gate
        
        if node[0] == 'PRED': 
            return Predicate(node[1], [self._term_to_obj(a, bounds) for a in node[2]])
        
        if node[0] == 'NOT':
            inner = self._to_ast(node[1], bounds)
            if inner is None: return None 
            if isinstance(inner, Predicate): 
                return Predicate(inner.name, inner.args, not inner.negated)
            return ('NOT', inner)
            
        if node[0] in ('FORALL', 'EXISTS'):
            # Ensure node[2] exists and is valid
            inner = self._to_ast(node[2], bounds | {node[1]})
            if inner is None: return None
            return (node[0], node[1], inner)
        
        # Add this for AND/OR/IFF/IMPLIES
        if node[0] in ('AND', 'OR', 'IMPLIES', 'IFF'):
            return (node[0], [self._to_ast(n, bounds) for n in node[1] if n is not None])

        return None


    def _term_to_obj(self, t, bounds):
        if t[0] == 'VAR' or t[1] in bounds: return Variable(t[1])
        if t[0] == 'CONST': return Constant(t[1])
        return Function(t[1], [self._term_to_obj(a, bounds) for a in t[2]])

    def _cnf(self, formula):
        def elim(n):
            if isinstance(n, Predicate): return n
            if n[0] == 'NOT': return ('NOT', elim(n[1]))
            if n[0] in ('FORALL', 'EXISTS'): return (n[0], n[1], elim(n[2]))
            args = [elim(a) for a in n[1]]
            if n[0] == 'IMPLIES': return ('OR', [('NOT', args[0]), args[1]])
            if n[0] == 'IFF': 
                return ('AND', [('OR', [('NOT', args[0]), args[1]]), ('OR', [('NOT', args[1]), args[0]])])
            return (n[0], args)

        def nnf(n):
            if isinstance(n, Predicate): return n
            if n[0] != 'NOT':
                return (n[0], n[1], nnf(n[2])) if n[0] in ('FORALL', 'EXISTS') else (n[0], [nnf(a) for a in n[1]])
            inner = n[1]
            if isinstance(inner, Predicate): return Predicate(inner.name, inner.args, not inner.negated)
            if inner[0] == 'NOT': return nnf(inner[1])
            if inner[0] == 'AND': return ('OR', [nnf(('NOT', a)) for a in inner[1]])
            if inner[0] == 'OR': return ('AND', [nnf(('NOT', a)) for a in inner[1]])
            if inner[0] == 'FORALL': return ('EXISTS', inner[1], nnf(('NOT', inner[2])))
            if inner[0] == 'EXISTS': return ('FORALL', inner[1], nnf(('NOT', inner[2])))
            return n

        def skolem(n, univs, sub):
            if isinstance(n, Predicate): 
                return Predicate(n.name, [apply_sub_term(a, sub) for a in n.args], n.negated)
            if n[0] == 'AND': return ('AND', [skolem(a, univs, sub) for a in n[1]])
            if n[0] == 'OR': return ('OR', [skolem(a, univs, sub) for a in n[1]])
            if n[0] == 'FORALL':
                self.var_count += 1
                nv = Variable(f"v{self.var_count}")
                # Replace the quantified variable with a unique variable name
                return skolem(n[2], univs + [nv], {**sub, n[1]: nv})
            if n[0] == 'EXISTS':
                self.sk_count += 1
                # If inside universals, it's a function; otherwise, it's a constant
                sk = Function(f"sk{self.sk_count}", univs) if univs else Constant(f"sk{self.sk_count}")
                return skolem(n[2], univs, {**sub, n[1]: sk})
            return n

        def apply_sub_term(t, sub):
            if isinstance(t, Variable) and t.name in sub: return sub[t.name]
            if isinstance(t, Function): return Function(t.name, [apply_sub_term(a, sub) for a in t.args])
            return t

        def dist(n):
            if isinstance(n, Predicate): return [frozenset([n])]
            if n[0] == 'AND':
                res = []
                for a in n[1]: res.extend(dist(a))
                return res
            if n[0] == 'OR':
                # Correctly handle distribution for list-based arguments
                import itertools
                child_clauses = [dist(a) for a in n[1]]
                return [frozenset().union(*comb) for comb in itertools.product(*child_clauses)]
            return []

        # --- The Execution Pipeline ---
        # 1. Eliminate Implies/Iff
        step1 = elim(formula)
        # 2. Push Negations inward (Negation Normal Form)
        step2 = nnf(step1)
        # 3. Remove quantifiers (Skolemize)
        step3 = skolem(step2, [], {})
        # 4. Distribute ORs over ANDs to get final Clauses
        return dist(step3)

    # Add this inside the TheoremProver class
    def is_tautology(self, literals):
        """
        Returns True if the clause contains both P and ¬P with the same arguments.
        Tautologies are logically useless in resolution refutation.
        """
        lits_list = list(literals)
        for i in range(len(lits_list)):
            for j in range(i + 1, len(lits_list)):
                l1, l2 = lits_list[i], lits_list[j]
                if l1.name == l2.name and l1.args == l2.args and l1.negated != l2.negated:
                    return True
        return False

    def prove(self, kb_lines, theorem_str):
        # 0. Reset state for a fresh run
        Clause.reset()
        self.var_count = 0
        self.sk_count = 0
        
        # Store kb_lines locally for this run
        self.kb_lines = kb_lines

        # 1. Setup Background Knowledge (Axioms + KB)
        background_clauses = []
        for line in (self.base_axioms + self.kb_lines):
            ast = self._to_ast(self._parse(self._tokenize(line)), set())
            
            # print(f"DEBUG: Processing line -> {line}") # ADD THIS
            tokens = self._tokenize(line)
            ast_raw = self._parse(tokens)
            if ast_raw is None:
                print(f"ERROR: Parser returned None for: {line}")
                continue

            for lits in self._cnf(ast): # type: ignore
                if not self.is_tautology(lits):
                    background_clauses.append(Clause(lits))

        # 2. Setup Set of Support (SoS) with the Negated Goal
        sos_clauses = []
        goal_ast = self._to_ast(self._parse(self._tokenize(theorem_str)), set())
        negated_goal = nnf_neg(goal_ast)
        for lits in self._cnf(negated_goal):
            if not self.is_tautology(lits):
                sos_clauses.append(Clause(lits))

        # Combine into the main list
        all_clauses = background_clauses + sos_clauses
        # Track which indices belong to the Set of Support
        sos_indices = set(range(len(background_clauses), len(all_clauses)))
        
        seen = set(c.literals for c in all_clauses)
        proof_log = []
        
        # 3. Main Resolution Loop
        i = 0
        limit = 3000 
        while i < len(all_clauses) and limit > 0:
            
            # --- UNIT PREFERENCE / SHORTEST CLAUSE STRATEGY ---
            if i % 5 == 0:
                # Sort upcoming SoS clauses by length to find contradiction faster
                remaining_sos = [(idx, all_clauses[idx]) for idx in sos_indices if idx >= i]
                if remaining_sos:
                    remaining_sos.sort(key=lambda x: len(x[1].literals))
                    new_order = [item[1] for item in remaining_sos]
                    non_sos = [c for idx, c in enumerate(all_clauses[i:]) if (i + idx) not in sos_indices]
                    all_clauses[i:] = new_order + non_sos

            current_clause = all_clauses[i]

            for j in range(i):
                limit -= 1
                target_clause = all_clauses[j]

                # --- SET OF SUPPORT STRATEGY ---
                # One parent must be from the SoS to keep search relevant
                if i not in sos_indices and j not in sos_indices:
                    continue

                for res_lits in self._resolve(current_clause, target_clause):
                    if res_lits in seen or self.is_tautology(res_lits):
                        continue

                    new_clause = Clause(res_lits, parents=(current_clause.id, target_clause.id))
                    
                    all_clauses.append(new_clause)
                    sos_indices.add(len(all_clauses) - 1)
                    proof_log.append({"result": new_clause, "from": (current_clause.id, target_clause.id)})
                    seen.add(res_lits)

                    if new_clause.is_empty():
                        return True, proof_log, all_clauses
            i += 1

        return False, proof_log, all_clauses

    def _resolve(self, c1, c2):
        res = []
        for l1 in c1.literals:
            for l2 in c2.literals:
                if l1.name == l2.name and l1.negated != l2.negated:
                    sub = self._unify_lists(l1.args, l2.args, {})
                    if sub is not None:
                        nl = set()
                        for l in (set(c1.literals) | set(c2.literals)):
                            if l != l1 and l != l2: nl.add(self._apply_sub_pred(l, sub))
                        res.append(frozenset(nl))
        return res

    def _unify_lists(self, l1, l2, s):
        for a, b in zip(l1, l2):
            s = self._unify(a, b, s)
            if s is None: return None
        return s

    def _unify(self, u, v, s):
        if s is None: return None
        if u == v: return s
        if isinstance(u, Variable): return self._unify_var(u, v, s)
        if isinstance(v, Variable): return self._unify_var(v, u, s)
        if isinstance(u, (Function, Predicate)) and isinstance(v, (Function, Predicate)):
            return self._unify_lists(u.args, v.args, s) if u.name == v.name and len(u.args) == len(v.args) else None
        return None

    def _unify_var(self, var, val, s):
        if var.name in s: return self._unify(s[var.name], val, s)
        if isinstance(val, Variable) and val.name in s: return self._unify(var, s[val.name], s)
        if self._occur_check(var, val, s): return None
        return {**s, var.name: val}

    def _occur_check(self, var, val, s):
        if var == val: return True
        if isinstance(val, Variable) and val.name in s: return self._occur_check(var, s[val.name], s)
        if isinstance(val, Function): return any(self._occur_check(var, a, s) for a in val.args)
        return False

    def _apply_sub_pred(self, p, s):
        return Predicate(p.name, [self._apply_sub_term(a, s) for a in p.args], p.negated)

    def _apply_sub_term(self, t, s):
        if isinstance(t, Variable) and t.name in s: return self._apply_sub_term(s[t.name], s)
        if isinstance(t, Function): return Function(t.name, [self._apply_sub_term(a, s) for a in t.args])
        return t

def nnf_neg(n):
    if isinstance(n, Predicate): return Predicate(n.name, n.args, not n.negated)
    if n[0] == 'NOT': return n[1]
    if n[0] == 'AND': return ('OR', [nnf_neg(a) for a in n[1]])
    if n[0] == 'OR': return ('AND', [nnf_neg(a) for a in n[1]])
    if n[0] == 'FORALL': return ('EXISTS', n[1], nnf_neg(n[2]))
    if n[0] == 'EXISTS': return ('FORALL', n[1], nnf_neg(n[2]))
    if n[0] == 'IMPLIES': return ('AND', [n[1][0], nnf_neg(n[1][1])])