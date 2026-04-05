import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext, filedialog
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import networkx as nx
from typing import List, Set

# Ensure your atp.py is in the same directory
from atp import TheoremProver, Clause

class SymbolPalette(tk.Frame):
    """Palette of logical symbols for easy insertion."""
    SYMBOLS = [
        ('∀', 'Universal quantifier (forall)'),
        ('∃', 'Existential quantifier (exists)'),
        ('¬', 'Negation (not)'),
        ('∧', 'Conjunction (and)'),
        ('∨', 'Disjunction (or)'),
        ('→', 'Implication (if-then)'),
        ('↔', 'Biconditional (iff)'),
    ]
    
    def __init__(self, parent, target_widget, **kwargs):
        super().__init__(parent, **kwargs)
        self.target = target_widget
        tk.Label(self, text="Symbols:", bg=self["bg"]).pack(side=tk.LEFT, padx=(0, 5))
        for symbol, tooltip in self.SYMBOLS:
            btn = tk.Button(self, text=symbol, width=3, 
                           command=lambda s=symbol: self.insert_symbol(s))
            btn.pack(side=tk.LEFT, padx=2)

    def insert_symbol(self, symbol: str):
        if isinstance(self.target, tk.Text):
            self.target.insert(tk.INSERT, symbol)
        elif isinstance(self.target, tk.Entry):
            pos = self.target.index(tk.INSERT)
            self.target.insert(pos, symbol)
        self.target.focus_set()

class ExamplesPanel(tk.Frame):
    """Panel with set-based example problems."""
    EXAMPLES = {
        "Subset Transitivity": {
            "kb": ["Subset(SetA, SetB)", "Subset(SetB, SetC)"],
            "goal": "Subset(SetA, SetC)"
        },
        "Union Membership": {
            "kb": ["In(Element, SetA)"],
            "goal": "In(Element, Union(SetA, SetB))"
        },
        "Set Equality": {
            "kb": ["Subset(A, B)", "Subset(B, A)"],
            "goal": "Equals(A, B)"
        },
        "Empty Set Check": {
            "kb": ["In(x, S)"],
            "goal": "¬Equals(S, EmptySet)"
        },
        "Intersection Proof": {
            "kb": ["In(Element, Intersect(SetA, SetB))"],
            "goal": "In(Element, SetA)"
        },
        "Set Difference": {
            "kb": ["In(x, Difference(A, B))"],
            "goal": "¬In(x, B)"
        },
        "Universal Set": {
            "kb": ["Subset(S, UniversalSet)"], # This is always true by axioms
            "goal": "forall x (In(x, S) implies In(x, UniversalSet))"
        },
        "Subset Transitivity": {
            "kb": ["Subset(SetA, SetB)", "Subset(SetB, SetC)"],
            "goal": "Subset(SetA, SetC)"
        },
    }
    
    def __init__(self, parent, load_callback, **kwargs):
        super().__init__(parent, **kwargs)
        self.load_callback = load_callback
        tk.Label(self, text="Load Set Theory Example:", bg=self["bg"], 
                font=('Arial', 9, 'bold')).pack(anchor='w')
        self.example_var = tk.StringVar()
        self.combo = ttk.Combobox(self, textvariable=self.example_var,
                                 values=list(self.EXAMPLES.keys()),
                                 state='readonly', width=30)
        self.combo.pack(pady=5, fill=tk.X)
        self.combo.bind('<<ComboboxSelected>>', lambda e: self.load_callback(self.EXAMPLES[self.example_var.get()]))

class ProofGraphPanel(tk.Frame):
    """Visualizes the resolution steps."""
    def __init__(self, parent, **kwargs):
        super().__init__(parent, **kwargs)
        self.fig, self.ax = plt.subplots(figsize=(10, 8))
        self.canvas = FigureCanvasTkAgg(self.fig, master=self)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    def clear(self):
        self.ax.clear()
        self.canvas.draw()

    def draw_proof(self, proof_log, all_clauses, initial_count):
        self.ax.clear()
        if not all_clauses: return
        G = nx.DiGraph()
        labels, node_colors, relevant = {}, [], set()
        
        if all_clauses[-1].is_empty():
            self._trace(all_clauses[-1].id, proof_log, relevant)
        else:
            relevant = {c.id for c in all_clauses}

        for c in all_clauses:
            if c.id not in relevant: continue
            G.add_node(c.id)
            labels[c.id] = str(c)
            node_colors.append('#2ecc71' if c.is_empty() else ('#3498db' if c.id < initial_count else '#e67e22'))

        for step in proof_log:
            if step["result"].id in relevant:
                G.add_edge(step["from"][0], step["result"].id)
                G.add_edge(step["from"][1], step["result"].id)

        pos = nx.spring_layout(G, k=2)
        nx.draw(G, pos, labels=labels, with_labels=True, node_color=node_colors, 
                node_size=3000, font_size=7, ax=self.ax, node_shape='s')
        self.canvas.draw()

    def _trace(self, cid, log, rel):
        if cid in rel: return
        rel.add(cid)
        for s in log:
            if s["result"].id == cid:
                self._trace(s["from"][0], log, rel)
                self._trace(s["from"][1], log, rel)

class ATPApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Set Theory Automated Theorem Prover")
        self.root.geometry("1400x900")
        self.prover = TheoremProver(include_set_axioms=True)
        self._setup_ui()

    def _setup_ui(self):
        main_paned = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_paned.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        left_frame = tk.Frame(main_paned, bg="#f5f5f5", padx=15, pady=15)
        right_frame = tk.Frame(main_paned, bg="white")
        main_paned.add(left_frame, weight=1)
        main_paned.add(right_frame, weight=2)

        tk.Label(left_frame, text="ATP: Set Theory Engine", font=('Arial', 14, 'bold'), bg="#f5f5f5").pack(pady=(0, 10))
        
        ExamplesPanel(left_frame, self.load_example, bg="#f5f5f5").pack(fill=tk.X, pady=10)

        kb_f = tk.LabelFrame(left_frame, text="Knowledge Base", bg="#f5f5f5", padx=5, pady=5)
        kb_f.pack(fill=tk.X)
        self.kb_input = scrolledtext.ScrolledText(kb_f, height=8, width=40, font=('Courier', 10))
        SymbolPalette(kb_f, self.kb_input, bg="#f5f5f5").pack(fill=tk.X)
        self.kb_input.pack(fill=tk.X)

        gl_f = tk.LabelFrame(left_frame, text="Goal to Prove", bg="#f5f5f5", padx=5, pady=5)
        gl_f.pack(fill=tk.X, pady=10)
        self.goal_input = tk.Entry(gl_f, font=('Courier', 10))
        SymbolPalette(gl_f, self.goal_input, bg="#f5f5f5").pack(fill=tk.X)
        self.goal_input.pack(fill=tk.X)

        tk.Button(left_frame, text="RUN PROOF", command=self.run_proof, bg="#27ae60", fg="white", font=('Arial', 12, 'bold')).pack(fill=tk.X, pady=5)
        tk.Button(left_frame, text="Clear All", command=self.clear_all, bg="#e74c3c", fg="white").pack(fill=tk.X)

        self.log_area = scrolledtext.ScrolledText(left_frame, height=15, state='disabled', font=('Courier', 9))
        self.log_area.pack(fill=tk.BOTH, expand=True, pady=10)
        self.graph_panel = ProofGraphPanel(right_frame, bg="white")
        self.graph_panel.pack(fill=tk.BOTH, expand=True)

    def load_example(self, ex):
        self.kb_input.delete('1.0', tk.END)
        self.kb_input.insert(tk.INSERT, '\n'.join(ex['kb']))
        self.goal_input.delete(0, tk.END)
        self.goal_input.insert(0, ex['goal'])

    def clear_all(self):
        self.kb_input.delete('1.0', tk.END)
        self.goal_input.delete(0, tk.END)
        self.graph_panel.clear()

    def log(self, msg):
        self.log_area.config(state='normal')
        self.log_area.insert(tk.END, msg + "\n")
        self.log_area.config(state='disabled')
        self.log_area.see(tk.END)

    def run_proof(self):
        self.log_area.config(state='normal')
        self.log_area.delete('1.0', tk.END)
        self.log_area.config(state='disabled')
        self.graph_panel.clear()
        
        kb = [l.strip() for l in self.kb_input.get("1.0", tk.END).split('\n') if l.strip()]
        goal = self.goal_input.get().strip()
        
        if not kb or not goal: return

        self.log("Initializing Set Theory Axioms...")
        success, proof_log, all_clauses = self.prover.prove(kb, goal)
        initial_count = len(all_clauses) - len(proof_log)

        self.log(f"Generated {initial_count} initial clauses.")
        for step in proof_log:
            self.log(f"Derived: {step['result']}")

        if success:
            messagebox.showinfo("Success", "Goal Proved via Contradiction!")
        else:
            messagebox.showwarning("Failed", "Could not find a proof.")
        self.graph_panel.draw_proof(proof_log, all_clauses, initial_count)

if __name__ == "__main__":
    root = tk.Tk()
    app = ATPApp(root)
    root.mainloop()