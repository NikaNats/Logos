import asyncio
import random
from dataclasses import dataclass
from typing import Dict, Any, Callable, List

# --- PART I: THE DEFINITION OF TIME (CHRONOS VS KAIROS) ---

class Chronos:
    """Standard linear time (clock ticks)."""
    @staticmethod
    async def fast(milliseconds):
        """Ascetic pause (sleep)."""
        await asyncio.sleep(milliseconds / 1000)

# --- PART II: THE SYNOD (CONCILIAR STATE) ---

class SynodalState:
    def __init__(self):
        # The shared reality (The State)
        self._essence: Dict[str, Any] = {}
        
        # The mechanism of notification (The Bells)
        # In secular terms: A Condition Variable
        self._consensus_lock = asyncio.Condition()
        
        # Log of history (Tradition)
        self._history: List[str] = []

    async def petition(self, key: str, value: Any, petitioner_name: str):
        """
        0x20 PETITION implementation.
        A thread requests to update the truth.
        """
        async with self._consensus_lock:
            # 1. Update the Reality
            old_val = self._essence.get(key, "Void")
            self._essence[key] = value
            
            # 2. Record the act in Tradition
            record = f"[{petitioner_name}] petitioned change: {key} ({old_val} -> {value})"
            self._history.append(record)
            print(record)
            
            # 3. Proclaim the Good News (Notify All)
            # This wakes up the Hesychasts who are waiting for a change.
            self._consensus_lock.notify_all()

    def read(self, key: str):
        """Standard read (Beholding)."""
        return self._essence.get(key)

    async def wait_for_kairos(self, predicate: Callable[[], bool], petitioner_name: str):
        """
        Hesychastic Waiting.
        The thread waits until the 'predicate' (Kairos condition) becomes True.
        """
        async with self._consensus_lock:
            print(f"[{petitioner_name}] enters Hesychasm... (Waiting for Kairos)")
            
            # This is the core of Synergy.
            # The thread yields control (humility) until the Synod notifies it.
            # wait_for automatically releases the lock and waits.
            await self._consensus_lock.wait_for(predicate)
            
            print(f"[{petitioner_name}] The Kairos has arrived! Proceeding...")

# --- PART III: THE LITURGY (DEMONSTRATION) ---

# Global instance of the Synod
synod = SynodalState()

async def bell_ringer_monk(name: str):
    """
    This monk's job is to ring the bell 3 times.
    He petitions the state to update 'bell_count'.
    """
    for i in range(1, 4):
        await Chronos.fast(random.randint(500, 1500)) # Work takes time
        await synod.petition("bell_count", i, name)

async def morning_service_monk(name: str):
    """
    This monk cannot start the liturgy until the bell has rung 3 times.
    He does not poll (waste CPU); he waits for Kairos.
    """
    # THE KAIROS CONDITION: lambda: bell_count == 3
    # This defines "The Right Moment".
    def is_liturgy_time():
        count = synod.read("bell_count")
        return count == 3

    # Enter Hesychasm
    await synod.wait_for_kairos(is_liturgy_time, name)
    
    # When he wakes, the condition is guaranteed to be true.
    print(f"[{name}] The 3rd Bell has rung. Blessed is the Kingdom!")

async def abbot_monk(name: str):
    """
    The Abbot monitors the bell. If it rings even once, he prepares the censer.
    """
    def is_first_bell():
        val = synod.read("bell_count")
        return val is not None and val >= 1

    await synod.wait_for_kairos(is_first_bell, name)
    print(f"[{name}] First bell heard. Preparing the Censer.")

async def main_liturgy():
    print("--- BEGINNING THE OFFICE OF MATINS ---")
    
    # Initialize state
    await synod.petition("bell_count", 0, "Creation")

    # Create the Synergy of threads (Tasks)
    # They run concurrently, but cooperatively.
    await asyncio.gather(
        morning_service_monk("Fr. Seraphim"),
        abbot_monk("Fr. Paisios"),
        bell_ringer_monk("Br. John")
    )
    
    print("--- SERVICE CONCLUDED ---")

if __name__ == "__main__":
    try:
        # Run the event loop
        asyncio.run(main_liturgy())
    except KeyboardInterrupt:
        pass
