import sys
import z3
from lark import Lark, Transformer, v_args
from dataclasses import dataclass, field
from typing import Dict, List, Optional

# --- PART I: THE CANON (Dogmatic Definitions) ---

@dataclass
class HolyNature:
    """Represents a Type Definition (Apophatic Theology).
    We define a type by what it must NOT be."""
    name: str
    constraints: List[tuple]  # List of (operator, threshold)

    def generate_dogma(self, z3_var):
        """Converts the Nature into Z3 constraints (The Good Path)."""
        rules = []
        for op, val in self.constraints:
            # Apophatic inversion: The code says "not x < 0", 
            # so the Dogma is "x >= 0".
            if op == "<": rules.append(z3_var >= val)
            elif op == ">": rules.append(z3_var <= val)
            elif op == "<=": rules.append(z3_var > val)
            elif op == ">=": rules.append(z3_var < val)
            elif op == "==": rules.append(z3_var != val)
            elif op == "!=": rules.append(z3_var == val)
        return z3.And(*rules)

    def generate_anathema(self, z3_var):
        """Converts the Nature into the Definition of Sin (The Bad Path).
        Used to check if a violation is possible."""
        sins = []
        for op, val in self.constraints:
            # The code says "not x < 0".
            # The Anathema (Sin) is "x < 0".
            if op == "<": sins.append(z3_var < val)
            elif op == ">": sins.append(z3_var > val)
            elif op == "<=": sins.append(z3_var <= val)
            elif op == ">=": sins.append(z3_var >= val)
            elif op == "==": sins.append(z3_var == val)
            elif op == "!=": sins.append(z3_var != val)
        return z3.Or(*sins)

# --- PART II: THE CONSCIENCE (State Management) ---

class SpiritualState:
    """Tracks variables in the current scope symbolically."""
    def __init__(self, parent=None):
        self.parent = parent
        self.variables: Dict[str, z3.ExprRef] = {}
        self.types: Dict[str, HolyNature] = {}

    def resolve(self, name):
        if name in self.variables:
            return self.variables[name]
        if self.parent:
            return self.parent.resolve(name)
        raise Exception(f"Ontological Error: The spirit '{name}' has not been summoned.")

    def get_type(self, name):
        if name in self.types:
            return self.types[name]
        if self.parent:
            return self.parent.get_type(name)
        return None

    def declare(self, name, nature: HolyNature, z3_expr):
        self.variables[name] = z3_expr
        self.types[name] = nature

# --- PART III: THE TRIBUNAL (The Diakrisis Engine) ---

class DiakrisisEngine:
    def __init__(self):
        self.solver = z3.Solver()
        self.global_canon: Dict[str, HolyNature] = {}
        # Pre-define the 'HolyInt' archetype
        self.global_canon["HolyInt"] = HolyNature("HolyInt", [("<", 0)]) # Must not be negative
        self.state = SpiritualState()
        self.path_conditions = [] # Stack of conditions (e.g., inside 'if' blocks)

    def register_essence(self, name, constraints):
        """Defines a new Type."""
        self.global_canon[name] = HolyNature(name, constraints)
        print(f"[Dogma] Defined Essence '{name}' with {len(constraints)} restrictions.")

    def confess_assignment(self, name, type_name, expr_node):
        """
        The Core of Diakrisis.
        Before 'name' can accept 'expr_node', we must prove it acts within its Nature.
        """
        # 1. Evaluate the expression symbolically
        z3_val = self._evaluate_expr(expr_node)
        
        # 2. Look up the Dogma for this type
        nature = self.global_canon.get(type_name)
        if not nature:
            raise Exception(f"Heresy: Unknown nature '{type_name}'.")

        # 3. Create a hypothetical world where the assignment happens
        self.solver.push()
        
        # 4. Add the current reality (Path Conditions and Dogmas)
        # Add dogmas of all variables in the state
        current_state = self.state
        while current_state:
            for var_name, z3_var in current_state.variables.items():
                var_nature = current_state.types.get(var_name)
                if var_nature:
                    self.solver.add(var_nature.generate_dogma(z3_var))
            current_state = current_state.parent

        # e.g., "We are inside an if(x > 5) block"
        for cond in self.path_conditions:
            self.solver.add(cond)

        # 5. THE INTERROGATION
        # We ask: "Is it possible for the value to commit a Sin?"
        # Sin = The Anathema of the Nature
        sin = nature.generate_anathema(z3_val)
        self.solver.add(sin)

        # 6. The Verdict
        result = self.solver.check()
        
        if result == z3.sat:
            # We found a counter-example. The code IS capable of sin.
            model = self.solver.model()
            self.solver.pop() # Restore state
            raise Exception(
                f"\n!!! ANATHEMA !!!\n"
                f"Spiritual Direction: The essence '{name}' of nature '{type_name}' is corrupt.\n"
                f"Reason: It is possible to violate the constraint.\n"
                f"Proof of Sin: If the inputs are {model}, the value becomes sinful.\n"
                f"Penance: You must guard this assignment with a 'try/repent' or 'if' check."
            )
        
        # 7. Absolution
        self.solver.pop() # Restore state
        # Commit the assignment to the state
        self.state.declare(name, nature, z3_val)
        print(f"[Absolution] Assignment to '{name}' is ontologically pure.")

    def enter_conditional(self, condition_node):
        """Handles 'if' blocks by adding constraints to the solver scope."""
        cond = self._evaluate_expr(condition_node)
        self.path_conditions.append(cond)
        
    def exit_conditional(self):
        self.path_conditions.pop()

    def _evaluate_expr(self, node):
        """Recursively turns AST nodes into Z3 expressions."""
        if isinstance(node, int):
            return z3.IntVal(node)
        if isinstance(node, str):
            # It's a variable name
            return self.state.resolve(node)
        if isinstance(node, tuple):
            op, left, right = node
            z_left = self._evaluate_expr(left)
            z_right = self._evaluate_expr(right)
            
            if op == "+": return z_left + z_right
            if op == "-": return z_left - z_right
            if op == "*": return z_left * z_right
            if op == "/": return z_left / z_right # Note: Z3 integer division
            if op == ">": return z_left > z_right
            if op == "<": return z_left < z_right
            if op == "==": return z_left == z_right
            if op == "!=": return z_left != z_right
            if op == "<=": return z_left <= z_right
            if op == ">=": return z_left >= z_right
            if op == "%": return z_left % z_right
        
        # For external inputs (witness), we create a fresh free variable
        if hasattr(node, "type") and node.type == "WITNESS_CALL":
            return z3.Int(f"input_{node.value}")
            
        return z3.IntVal(0)

# --- PART IV: THE LITURGY (Example Runner) ---

def run_demonstration():
    engine = DiakrisisEngine()

    print("--- STEP 1: DEFINING DOGMA ---")
    # Define a 'MonkCount' type: Cannot be negative, cannot exceed 100
    engine.register_essence("MonkCount", [("<", 0), (">", 100)])

    print("\n--- STEP 2: THE FIRST CONFESSION (Safe Code) ---")
    # Code: essence novices : MonkCount = 10;
    try:
        # AST representation: 10
        engine.confess_assignment("novices", "MonkCount", 10)
    except Exception as e:
        print(e)

    print("\n--- STEP 3: THE TEMPTATION (Unsafe Input) ---")
    # Code: essence input_val : HolyInt = witness("Give number");
    # Code: essence new_monks : MonkCount = input_val;
    # This should FAIL because 'input_val' could be 500, which violates MonkCount (>100)
    
    # 1. We create a generic input variable (could be anything)
    input_z3 = z3.Int("user_input") 
    engine.state.declare("input_val", engine.global_canon["HolyInt"], input_z3)
    
    try:
        print("Attempting: new_monks = input_val (where input_val is any positive int)")
        engine.confess_assignment("new_monks", "MonkCount", "input_val")
    except Exception as e:
        print(e)

    print("\n--- STEP 4: THE REPENTANCE (Guarded Code) ---")
    # Code: 
    # if (input_val <= 100) {
    #    new_monks = input_val;
    # }
    
    print("Applying Guard: if (input_val <= 100)...")
    
    # AST: ("<=", "input_val", 100)
    condition = ("<=", "input_val", 100) 
    
    # Enter the 'if' block
    engine.enter_conditional(condition)
    
    try:
        print("Re-attempting: new_monks = input_val (inside guard)")
        engine.confess_assignment("new_monks", "MonkCount", "input_val")
    except Exception as e:
        print(e)
    
    engine.exit_conditional()

if __name__ == "__main__":
    run_demonstration()
