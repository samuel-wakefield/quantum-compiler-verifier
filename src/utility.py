from circuit import QCircuit, QGate
def next_gate(circuit: QCircuit, gate_idx: int) -> int:
    """returns the index of the next gate in the circuit which shares a qubit with the gate at index 'gate_idx'

    Args:
        circuit (QCircuit): circuit to iterate over
        gate_idx (int): index of the gate we compare with

    Returns:
        int: index of the next gate after gate_idx which shares a qubit
    """
    gate = circuit.gates[gate_idx]
    qubits = gate.qubits
    for i in range(gate_idx, len(circuit.gates)):
        new_gate = circuit.gates[i]
        new_qubits = new_gate.qubits
        
        for qubit in new_qubits:
            if qubit in qubits:
                return i
    
    return None # what do we do if no gate has a matching qubit?
        