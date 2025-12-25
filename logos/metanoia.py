import copy
from dataclasses import dataclass, field
from typing import Dict, Any, List

# --- PART I: THE DEFINITION OF SIN ---

class Hamartia(Exception):
    """
    Standard languages call this 'Exception'.
    We call it Hamartia: 'Missing the mark'.
    """
    def __init__(self, message, spiritual_severity=1):
        self.message = message
        self.severity = spiritual_severity
    
    def __str__(self):
        return f"[Hamartia Level {self.severity}] {self.message}"

# --- PART II: THE SOUL (Memory Management) ---

class Soul:
    """
    Represents the memory state of the program.
    Unlike Python dicts, the Soul supports 'Transactional Rollback'.
    """
    def __init__(self, initial_state=None):
        self.memory: Dict[str, Any] = initial_state if initial_state else {}
        self.is_corrupted = False

    def remember(self, name, value):
        self.memory[name] = value

    def recall(self, name):
        if name not in self.memory:
            raise Hamartia(f"The essence '{name}' does not exist.")
        return self.memory[name]

    def create_icon(self):
        """
        Captures a snapshot (Icon) of the current state.
        This is Deep Copy - expensive, but necessary for purity.
        """
        return copy.deepcopy(self.memory)

    def restore_icon(self, icon):
        """
        Apokatastasis: Restoration of the state to the Icon.
        """
        self.memory = icon
        self.is_corrupted = False

    def __repr__(self):
        return str(self.memory)

# --- PART III: THE LITURGIST (Interpreter) ---

class LogosRuntime:
    def __init__(self):
        self.soul = Soul()

    def execute_liturgy(self, instructions):
        """
        The main loop. This would normally traverse an AST.
        Here we simulate it with a list of function calls.
        """
        for instruction in instructions:
            instruction(self)

    def run_try_repent(self, try_block_func, repent_block_func):
        """
        The implementation of:
        try { ... } repent { ... }
        """
        print("\n[Runtime] Entering Dangerous Contemplation (Try Block)...")
        
        # 1. NEPSIS (Watchfulness): Capture the Icon of the state
        # We save the state BEFORE the sin occurs.
        icon_of_creation = self.soul.create_icon()
        print(f"[Nepsis] State snapshot taken: {self.soul}")

        try:
            # 2. THE STRUGGLE: Execute the dangerous logic
            try_block_func(self)
            
            # If we reach here, no sin was committed.
            print("[Grace] Block completed without sin.")

        except Hamartia as sin:
            # 3. THE FALL: An error occurred.
            # In Python, self.soul might now contain partial, corrupted data.
            print(f"[Fall] Hamartia detected: {sin.message}")
            print(f"[Corrupted State] {self.soul}")

            # 4. APOKATASTASIS (Restoration): 
            # We reject the corrupted timeline. We restore the Icon.
            self.soul.restore_icon(icon_of_creation)
            print(f"[Restoration] State reverted to holiness: {self.soul}")

            # 5. METANOIA (Repentance):
            # We run the repent block. The state is now clean, so we can
            # attempt a new path without the baggage of the failed state.
            print("[Metanoia] Entering Repentance Block...")
            
            # We inject the sin into the scope so the monk knows what to repent of
            self.soul.remember("last_sin", sin.message)
            
            try:
                repent_block_func(self)
                print("[Absolution] Repentance complete. The Liturgy continues.")
            except Hamartia as mortal_sin:
                print(f"[Anathema] Sin committed during Repentance! The program dies.")
                raise mortal_sin

# --- PART IV: A DEMONSTRATION OF FAITH ---

def scenario_almsgiving():
    """
    Scenario: A monk is distributing bread.
    He attempts to give more than he has (Integer Underflow).
    """
    runtime = LogosRuntime()
    
    # Initial State
    runtime.soul.remember("bread_loaves", 5)
    runtime.soul.remember("hungry_people", 10)
    
    print(f"INITIAL STATE: {runtime.soul}")

    # --- THE LOGIC BLOCKS ---

    def dangerous_charity(rt: LogosRuntime):
        # The monk tries to give 1 loaf to everyone.
        # This loop causes side effects (modifying bread_loaves)
        # BEFORE it crashes.
        
        people = rt.soul.recall("hungry_people")
        
        for i in range(people):
            current_bread = rt.soul.recall("bread_loaves")
            print(f"  > Distributing loaf to person {i+1}...")
            
            # The Sin: Giving what you do not have
            if current_bread <= 0:
                raise Hamartia("Not enough bread!", spiritual_severity=5)
            
            # Side Effect: Modifying state
            rt.soul.remember("bread_loaves", current_bread - 1)

    def miracle_of_multiplication(rt: LogosRuntime):
        # The Repentance Logic
        # Notice: We start with 5 loaves again, NOT 0.
        # The runtime restored the loaves automatically.
        print("  > Lord, multiply this bread (Changing Strategy).")
        
        # We decide to break the loaves in half
        rt.soul.remember("bread_loaves", 10) # 5 loaves * 2 halves
        
        # Try distributing again
        current_bread = rt.soul.recall("bread_loaves")
        rt.soul.remember("bread_loaves", current_bread - rt.soul.recall("hungry_people"))

    # --- EXECUTION ---

    runtime.run_try_repent(dangerous_charity, miracle_of_multiplication)
    
    print(f"\nFINAL STATE: {runtime.soul}")

if __name__ == "__main__":
    scenario_almsgiving()
