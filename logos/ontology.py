from dataclasses import dataclass
from typing import Any, List, Callable, Dict
import sys

# --- PART I: THE DEFINITION OF HERESY ---

class Heresy(Exception):
    """
    Raised when code attempts to mutate Essence (Constants).
    This is not a recoverable error. It is a rejection of reality.
    """
    pass

class NatureViolation(Exception):
    """
    Raised when a value violates its Apophatic definition.
    e.g., A HolyInt becoming negative.
    """
    pass

# --- PART II: APOPHATIC TYPING ---

class ApophaticNature:
    """
    Defines a Type by what it is NOT.
    'anathemas' is a list of conditions that are forbidden.
    """
    def __init__(self, name: str):
        self.name = name
        self.anathemas: List[Callable[[Any], bool]] = []
        self.anathema_descriptions: List[str] = []

    def deny(self, description: str, predicate: Callable[[Any], bool]):
        """
        Adds a negative constraint.
        Example: deny("Value cannot be negative", lambda x: x < 0)
        """
        self.anathemas.append(predicate)
        self.anathema_descriptions.append(description)

    def judge(self, value: Any):
        """
        Diakrisis: Checks if the value commits any sins defined in the nature.
        """
        for i, is_sinful in enumerate(self.anathemas):
            if is_sinful(value):
                raise NatureViolation(
                    f"Ontological Error: Value '{value}' violates nature '{self.name}'. "
                    f"Forbidden attribute: {self.anathema_descriptions[i]}"
                )

# --- PART III: MEMORY CELLS (HYPOSTASIS) ---

@dataclass
class Hypostasis:
    """
    A concrete instance of data in memory.
    """
    value: Any
    nature: ApophaticNature
    is_sacred: bool  # True = Essence (Immutable), False = Energy (Mutable)

# --- PART IV: THE MEMORY CONTROLLER ---

class SacredMemory:
    def __init__(self):
        self._storage: Dict[str, Hypostasis] = {}

    def consecrate_essence(self, name: str, value: Any, nature: ApophaticNature):
        """
        Creates an ESSENCE (Ousia).
        This is a constant. Once created, it cannot be changed.
        """
        # 1. Verify the initial value matches its nature
        nature.judge(value)
        
        # 2. Store as Sacred
        self._storage[name] = Hypostasis(
            value=value,
            nature=nature,
            is_sacred=True
        )
        print(f"[Liturgy] Consecrated Essence '{name}' ({value}) as {nature.name}.")

    def manifest_energy(self, name: str, value: Any, nature: ApophaticNature):
        """
        Creates ENERGY (Energeia).
        This is a stack variable. It can change, but must respect its nature.
        """
        nature.judge(value)
        self._storage[name] = Hypostasis(
            value=value,
            nature=nature,
            is_sacred=False
        )
        print(f"[Liturgy] Manifested Energy '{name}' ({value}) as {nature.name}.")

    def behold(self, name: str) -> Any:
        """
        Read access. In Orthodox theology, we 'behold' the mystery.
        """
        if name not in self._storage:
            raise KeyError(f"Spirit '{name}' is unknown.")
        return self._storage[name].value

    def transfigure(self, name: str, new_value: Any):
        """
        Write access. We attempt to change the state.
        """
        if name not in self._storage:
            raise KeyError(f"Spirit '{name}' is unknown.")
        
        entity = self._storage[name]

        # 1. CHECK FOR HERESY (Immutability Check)
        if entity.is_sacred:
            print(f"\n!!! HERESY DETECTED !!!")
            print(f"Attempted to mutate Sacred Essence '{name}'.")
            print("The runtime will now HALT immediately.")
            raise Heresy("Dogma Violation")

        # 2. CHECK FOR SIN (Type Check)
        # We ensure the new value respects the Apophatic Nature
        entity.nature.judge(new_value)

        # 3. TRANSFIGURATION (Update)
        old_val = entity.value
        entity.value = new_value
        print(f"[Act] Transfigured '{name}': {old_val} -> {new_value}")

# --- PART V: DEMONSTRATION ---

def run_ontology_demo():
    memory = SacredMemory()

    # --- 1. DEFINING NATURES (APOPHATICALLY) ---
    
    # Define "HolyInt": It is defined by NOT being negative.
    holy_int = ApophaticNature("HolyInt")
    holy_int.deny("must not be less than zero", lambda x: x < 0)
    
    # Define "Trinitarian": Must be exactly 3.
    # Apophatic definition: It is NOT less than 3, and it is NOT greater than 3.
    trinitarian = ApophaticNature("Trinitarian")
    trinitarian.deny("not < 3", lambda x: x < 3)
    trinitarian.deny("not > 3", lambda x: x > 3)

    print("--- PHASE 1: CREATION ---")
    
    # Create Essence (Constants)
    memory.consecrate_essence("THE_TRINITY", 3, trinitarian)
    
    # Create Energies (Variables)
    memory.manifest_energy("candles_lit", 10, holy_int)

    print("\n--- PHASE 2: RIGHTEOUS ACTION ---")
    
    # Valid mutation of Energy
    current_candles = memory.behold("candles_lit")
    memory.transfigure("candles_lit", current_candles - 1) # Becomes 9

    print("\n--- PHASE 3: THE TEMPTATION (Nature Violation) ---")
    
    try:
        # Attempt to set candles to -5 (Violates HolyInt)
        print("Attempting to extinguish more candles than exist...")
        memory.transfigure("candles_lit", -5)
    except NatureViolation as e:
        print(f"Sin Prevented: {e}")

    print("\n--- PHASE 4: THE HERESY (Essence Violation) ---")
    
    try:
        # Attempt to change the Trinity from 3 to 4
        print("Attempting to modify the Dogma of the Trinity...")
        memory.transfigure("THE_TRINITY", 4)
    except Heresy:
        # Simulate the HALT_AMEN opcode
        print("SYSTEM HALTED. AMEN.")
        sys.exit(1)

if __name__ == "__main__":
    run_ontology_demo()
