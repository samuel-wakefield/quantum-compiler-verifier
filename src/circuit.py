from __future__ import annotations
from typing import List
class QGate:
    def __init__(self, name: str, qubits):
        self.name = name
        self.qubits = tuple(qubits)
        
class QCircuit:
    def __init__(self, gates: List[QGate] | None):
        self.gates = gates or []
    
    def append(self, gate: QGate):
        self.gates.append(gate)
        
    def delete(self, idx: int):
        del self.gates[idx]
    
    def copy(self) -> QCircuit:
        other = QCircuit(list(self.gates))
        return other
    
    def size(self) -> int:
        return len(self.gates)
