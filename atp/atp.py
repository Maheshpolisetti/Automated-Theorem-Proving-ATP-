# ---------- CORE DATA STRUCTURES ----------
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
    def __init__(self, literals, parents=None, is_sos=False):
        self.literals = frozenset(literals)
        self.id = Clause._id_counter
        Clause._id_counter += 1
        self.parents = parents
        self.is_sos = is_sos
    @staticmethod
    def reset(): Clause._id_counter = 0
    def is_empty(self): return len(self.literals) == 0
    def __repr__(self):
        if self.is_empty(): return "□"
        return f"C{self.id}: " + " ∨ ".join(map(repr, sorted(list(self.literals), key=lambda x: str(x))))
    def __hash__(self): return hash(self.literals)
    def __eq__(self, other): return isinstance(other, Clause) and self.literals == other.literals

class TheoremProver:
    def __init__(self, include_set_axioms=True):
        self.base_axioms = [
            "∀ax_v1 ¬In(ax_v1, EmptySet)",
            "∀ax_v1 In(ax_v1, UniversalSet)",
            "∀ax_v1 ∀ax_a ∀ax_b (In(ax_v1, Intersect(ax_a, ax_b)) ↔ (In(ax_v1, ax_a) ∧ In(ax_v1, ax_b)))",
            "∀ax_v1 ∀ax_a ∀ax_b (In(ax_v1, Union(ax_a, ax_b)) ↔ (In(ax_v1, ax_a) ∨ In(ax_v1, ax_b)))",
            "∀ax_a ∀ax_b (Subset(ax_a, ax_b) ↔ ∀ax_v1 (In(ax_v1, ax_a) → In(ax_v1, ax_b)))",
            "∀ax_v1 ∀ax_a ∀ax_b (In(ax_v1, Difference(ax_a, ax_b)) ↔ (In(ax_v1, ax_a) ∧ ¬In(ax_v1, ax_b)))",
            "∀ax_a ∀ax_b (Equals(ax_a, ax_b) ↔ (Subset(ax_a, ax_b) ∧ Subset(ax_b, ax_a)))",
            "∀ax_eq Equals(ax_eq, ax_eq)"  # Reflexivity is mathematically required for Paramodulation
        ] if include_set_axioms else []
        self.var_count = 0
        self.sk_count = 0
        self.std_var_count = 0

    def _tokenize(self, s):
        def rep(word, replacement):
            nonlocal s
            s = re.sub(r'(?i)\b' + word + r'\b', replacement, s)
            
        rep('forall', ' FORALL ')
        rep('exists', ' EXISTS ')
        rep('not', ' NOT ')
        rep('and', ' AND ')
        rep('or', ' OR ')
        rep('implies', ' IMPLIES ')
        rep('iff', ' IFF ')
        
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
            while peek() == 'IFF': consume(); node = ('IFF', [node, parse_implies()])
            return node
        def parse_implies():
            node = parse_or()
            while peek() == 'IMPLIES': consume(); node = ('IMPLIES', [node, parse_or()])
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
            if t == 'NOT': consume(); return ('NOT', parse_unary())
            if t in ('FORALL', 'EXISTS'):
                q, v = consume(), consume(); return (q, v, parse_unary())
            if t == '(': consume(); res = parse_formula(); consume(); return res
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
        if node is None: return None
        if node[0] == 'PRED': 
            return Predicate(node[1], [self._term_to_obj(a, bounds) for a in node[2]])
        if node[0] == 'NOT':
            inner = self._to_ast(node[1], bounds)
            if isinstance(inner, Predicate): 
                return Predicate(inner.name, inner.args, not inner.negated)
            return ('NOT', inner)
        if node[0] in ('AND', 'OR', 'IMPLIES', 'IFF'):
            return (node[0], [self._to_ast(n, bounds) for n in node[1]])
        if node[0] in ('FORALL', 'EXISTS'):
            return (node[0], node[1], self._to_ast(node[2], bounds | {node[1]}))
        return node 

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
            if n[0] == 'IFF': return ('AND', [('OR', [('NOT', args[0]), args[1]]), ('OR', [('NOT', args[1]), args[0]])])
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
        def skolem(n, univs, sub):
            if isinstance(n, Predicate): return Predicate(n.name, [apply_sub_term(a, sub) for a in n.args], n.negated)
            if n[0] == 'AND': return ('AND', [skolem(a, univs, sub) for a in n[1]])
            if n[0] == 'OR': return ('OR', [skolem(a, univs, sub) for a in n[1]])
            if n[0] == 'FORALL':
                self.var_count += 1
                nv = Variable(f"v{self.var_count}")
                return skolem(n[2], univs + [nv], {**sub, n[1]: nv})
            if n[0] == 'EXISTS':
                self.sk_count += 1
                sk = Function(f"sk{self.sk_count}", univs) if univs else Constant(f"sk{self.sk_count}")
                return skolem(n[2], univs, {**sub, n[1]: sk})
        def apply_sub_term(t, sub):
            if isinstance(t, Variable) and t.name in sub: return sub[t.name]
            if isinstance(t, Function): return Function(t.name, [apply_sub_term(a, sub) for a in t.args])
            return t

        def dist(n):
            if n is None: return [] 
            if isinstance(n, Predicate): 
                return [frozenset([n])]
            
            if n[0] == 'AND':
                res = []
                for a in n[1]:
                    d_res = dist(a)
                    if d_res: res.extend(d_res)
                return res
            
            if n[0] == 'OR':
                if len(n[1]) < 2: return dist(n[1][0])
                l, r = dist(n[1][0]), dist(n[1][1])
                return [li | ri for li in l for ri in r]
            
            return []
            
        f = skolem(nnf(elim(formula)), [], {})
        return dist(f)

    def is_tautology(self, literals):
        lits_list = list(literals)
        for i in range(len(lits_list)):
            for j in range(i + 1, len(lits_list)):
                l1, l2 = lits_list[i], lits_list[j]
                if l1.name == l2.name and l1.args == l2.args and l1.negated != l2.negated:
                    return True
        return False

    def _canonical(self, literals):
        """Alpha-equivalence normalization: Rename variables strictly by order of appearance."""
        def shape(t):
            if isinstance(t, Variable): return "_"
            if isinstance(t, Function): return f"{t.name}({','.join(shape(a) for a in t.args)})"
            return str(t)
        def lit_shape(l):
            return f"{'~' if l.negated else ''}{l.name}({','.join(shape(a) for a in l.args)})"
            
        lits_list = sorted(list(literals), key=lit_shape)
        var_map = {}
        counter = 0
        
        def canon_term(t):
            nonlocal counter
            if isinstance(t, Variable):
                if t.name not in var_map:
                    var_map[t.name] = f"_v{counter}"
                    counter += 1
                return Variable(var_map[t.name])
            if isinstance(t, Function):
                return Function(t.name, [canon_term(a) for a in t.args])
            return t
            
        nl = set()
        for p in lits_list:
            nl.add(Predicate(p.name, [canon_term(a) for a in p.args], p.negated))
        return frozenset(nl)

    def _standardize_apart(self, clause):
        """Rename variables entirely relative to this branch execution."""
        sub = {}
        def rename_term(t):
            if isinstance(t, Variable):
                if t.name not in sub:
                    self.std_var_count += 1
                    sub[t.name] = Variable(f"w{self.std_var_count}")
                return sub[t.name]
            if isinstance(t, Function):
                return Function(t.name, [rename_term(a) for a in t.args])
            return t
            
        new_lits = set()
        for l in clause.literals:
            new_lits.add(Predicate(l.name, [rename_term(a) for a in l.args], l.negated))
        return Clause(new_lits, parents=clause.parents, is_sos=clause.is_sos)

    def _theta_subsumes(self, c1, c2):
        """
        True if C1 theta-subsumes C2.
        For every literal in C1, there must be a literal in C2 such that C1 can unify with it
        with a substitution theta. The same theta must work for all literals in C1.
        """
        if len(c1.literals) > len(c2.literals):
            return False
            
        l1_list = list(c1.literals)
        
        # Freeze variables in C2 so they act as constants during unification
        def freeze(t):
            if isinstance(t, Variable): return Constant(f"$F_{t.name}")
            if isinstance(t, Function): return Function(t.name, [freeze(a) for a in t.args])
            return t
        
        l2_frozen = []
        for p in c2.literals:
            l2_frozen.append(Predicate(p.name, [freeze(a) for a in p.args], p.negated))
        
        def backtrack(idx, current_sub):
            if idx == len(l1_list):
                return True
            p1 = l1_list[idx]
            for p2 in l2_frozen:
                if p1.name == p2.name and p1.negated == p2.negated:
                    sub_copy = dict(current_sub) if current_sub else {}
                    new_sub = self._unify_lists(p1.args, p2.args, sub_copy)
                    if new_sub is not None:
                        if backtrack(idx + 1, new_sub):
                            return True
            return False
            
        return backtrack(0, {})

    def _is_subsumed(self, new_clause, clauses):
        for c in clauses:
            if self._theta_subsumes(c, new_clause):
                return True
        return False

    def _factor(self, clause):
        """Factor a clause by unifying literals within the same clause."""
        res_clauses = []
        lits = list(clause.literals)
        for i in range(len(lits)):
            for j in range(i + 1, len(lits)):
                l1, l2 = lits[i], lits[j]
                if l1.name == l2.name and l1.negated == l2.negated:
                    sub = self._unify_lists(l1.args, l2.args, {})
                    if sub is not None:
                        nl = set()
                        for p in lits:
                            nl.add(self._apply_sub_pred(p, sub))
                        res_clauses.append(Clause(nl, parents=(clause.id,), is_sos=clause.is_sos))
        return res_clauses

    def _score_term(self, term, current_depth):
        # Automatically penalize structurally deep/complex paths
        # This acts as an organic term depth limit stalling infinite generation limits
        score = (current_depth ** 2) * 5 
        
        if isinstance(term, Function):
            for arg in term.args:
                score += self._score_term(arg, current_depth + 1)
        return score

    def _score_clause(self, clause):
        """
        Dynamically rate the priority of a clause based on structural length
        and internal term nesting complexity!
        """
        score = len(clause.literals) * 10
        for lit in clause.literals:
            for arg in lit.args:
                score += self._score_term(arg, 1)
        return score

    def _extract_symbols(self, t, symbols):
        if isinstance(t, Function):
            if not t.name.startswith("sk"):
                symbols.add(t.name)
            for a in t.args:
                self._extract_symbols(a, symbols)

    def prove(self, kb_lines, theorem_str):
        Clause.reset()
        self.var_count = 0
        self.sk_count = 0
        self.std_var_count = 0
        self.kb_lines = kb_lines

        all_clauses = []
        seen_canon = set()
        
        # 1. Setup Background Knowledge (Axioms + KB)
        for line in (self.base_axioms + self.kb_lines):
            ast = self._to_ast(self._parse(self._tokenize(line)), set())
            for lits in self._cnf(ast):
                if not self.is_tautology(lits):
                    c = Clause(lits, is_sos=False)
                    canon = self._canonical(lits)
                    if canon not in seen_canon and not self._is_subsumed(c, all_clauses):
                        seen_canon.add(canon)
                        all_clauses.append(c)

        bg_clauses_count = len(all_clauses)

        # 2. Setup Set of Support (SoS) with the Negated Goal
        goal_ast = self._to_ast(self._parse(self._tokenize(theorem_str)), set())
        
        # We negate the goal natively via AST NOT wrapping
        neg_goal_ast = ('NOT', goal_ast)
        for lits in self._cnf(neg_goal_ast):  
            if not self.is_tautology(lits):
                c = Clause(lits, is_sos=True)
                canon = self._canonical(lits)
                if canon not in seen_canon and not self._is_subsumed(c, all_clauses):
                    seen_canon.add(canon)
                    all_clauses.append(c)

        proof_log = []
        
        i = 0
        limit = 50000 
        
        def add_clause(new_clause, current_clause_id, target_clause_id):
            nonlocal limit
            if new_clause.is_empty():
                proof_log.append({"result": new_clause, "from": (current_clause_id, target_clause_id)})
                all_clauses.append(new_clause)
                return True
                
            canon = self._canonical(new_clause.literals)
            if canon not in seen_canon and not self.is_tautology(new_clause.literals):
                if not self._is_subsumed(new_clause, all_clauses):
                    seen_canon.add(canon)
                    all_clauses.append(new_clause)
                    proof_log.append({"result": new_clause, "from": (current_clause_id, target_clause_id)})
                    limit -= 1
                    
                    # Also try to factor the new clause
                    factors = self._factor(new_clause)
                    for f in factors:
                        if add_clause(f, new_clause.id, new_clause.id):
                            return True
                        
            return False

        # Apply initial factoring
        for init_c in list(all_clauses):
            for f in self._factor(init_c):
                if add_clause(f, init_c.id, init_c.id):
                    return True, proof_log, all_clauses

        # 3. Main Resolution Loop
        while i < len(all_clauses) and limit > 0:
            
            # --- UNIT PREFERENCE / SHORTEST CLAUSE STRATEGY ---
            if i % 5 == 0:
                # Sort only the SoS portion of the queue (everything after bg_clauses_count)
                sort_start = max(i, bg_clauses_count)
                if sort_start < len(all_clauses):
                    remaining_sos = all_clauses[sort_start:]
                    remaining_sos.sort(key=lambda c: self._score_clause(c))
                    all_clauses[sort_start:] = remaining_sos

            current_clause = all_clauses[i]

            for j in range(i + 1): # i+1 implies that current clause targets itself for self-resolution technically (though we also factor)
                target_clause = all_clauses[j]

                # --- SET OF SUPPORT STRATEGY ---
                if not current_clause.is_sos and not target_clause.is_sos:
                    continue

                # Standardize apart variables in clauses
                c1 = self._standardize_apart(current_clause)
                c2 = self._standardize_apart(target_clause)

                for res_lits in self._resolve(c1, c2):
                    new_clause = Clause(res_lits, parents=(current_clause.id, target_clause.id), is_sos=True) # Resolvent is always SoS
                    if add_clause(new_clause, current_clause.id, target_clause.id):
                        return True, proof_log, all_clauses
                        
                for res_lits in self._paramodulate(c1, c2):
                    new_clause = Clause(res_lits, parents=(current_clause.id, target_clause.id), is_sos=True)
                    if add_clause(new_clause, current_clause.id, target_clause.id):
                        return True, proof_log, all_clauses
                        
                for res_lits in self._paramodulate(c2, c1):
                    new_clause = Clause(res_lits, parents=(target_clause.id, current_clause.id), is_sos=True)
                    if add_clause(new_clause, target_clause.id, current_clause.id):
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

    def _paramodulate_term(self, term, s, t, current_sub):
        results = []
        sub_copy = dict(current_sub) if current_sub else {}
        new_sub = self._unify(term, s, sub_copy)
        if new_sub is not None:
            results.append((t, new_sub))
            
        if isinstance(term, Function):
            for i, arg in enumerate(term.args):
                for new_arg, new_s in self._paramodulate_term(arg, s, t, current_sub):
                    new_args = list(term.args)
                    new_args[i] = new_arg
                    results.append((Function(term.name, new_args), new_s))
        return results

    def _paramodulate_pred(self, pred, s, t, current_sub):
        results = []
        for i, arg in enumerate(pred.args):
            for new_arg, new_s in self._paramodulate_term(arg, s, t, current_sub):
                new_args = list(pred.args)
                new_args[i] = new_arg
                results.append((Predicate(pred.name, new_args, pred.negated), new_s))
        return results

    def _paramodulate(self, c1, c2):
        res = []
        for l1 in c1.literals:
            if l1.name == "Equals" and not l1.negated and len(l1.args) == 2:
                for direction in [(0, 1), (1, 0)]:
                    s, t = l1.args[direction[0]], l1.args[direction[1]]
                    
                    # Restrict explosion: Do not paramodulate FROM pure variables directly!
                    if isinstance(s, Variable): continue
                    
                    for l2 in c2.literals:
                        for new_l2, sub in self._paramodulate_pred(l2, s, t, {}):
                            nl = set()
                            nl.add(self._apply_sub_pred(new_l2, sub))
                            for l in c1.literals:
                                if l != l1: nl.add(self._apply_sub_pred(l, sub))
                            for l in c2.literals:
                                if l != l2: nl.add(self._apply_sub_pred(l, sub))
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
        
        # Apply current substitutions before identifying variable unify
        if isinstance(u, Variable) and u.name in s: return self._unify(s[u.name], v, s)
        if isinstance(v, Variable) and v.name in s: return self._unify(u, s[v.name], s)
        
        if isinstance(u, Variable): return self._unify_var(u, v, s)
        if isinstance(v, Variable): return self._unify_var(v, u, s)
        if isinstance(u, (Function, Predicate)) and isinstance(v, (Function, Predicate)):
            return self._unify_lists(u.args, v.args, s) if u.name == v.name and len(u.args) == len(v.args) else None
        return None

    def _unify_var(self, var, val, s):
        if self._occur_check(var, val, s): return None
        s[var.name] = val
        return s

    def _occur_check(self, var, val, s):
        if var == val: return True
        if isinstance(val, Variable) and val.name in s: return self._occur_check(var, s[val.name], s)
        if isinstance(val, Function): return any(self._occur_check(var, a, s) for a in val.args)
        return False

    def _apply_sub_pred(self, p, s):
        return Predicate(p.name, [self._apply_sub_term(a, s) for a in p.args], p.negated)

    def _apply_sub_term(self, t, s):
        if isinstance(t, Variable):
            cur = t
            while isinstance(cur, Variable) and cur.name in s:
                cur = s[cur.name]
            if isinstance(cur, Function):
                return Function(cur.name, [self._apply_sub_term(a, s) for a in cur.args])
            return cur
        if isinstance(t, Function): return Function(t.name, [self._apply_sub_term(a, s) for a in t.args])
        return t

