from circuit import QCircuit, QGate
from utility import next_gate

class CX_Cancellation:
    def run(self, input: QCircuit): # input = remain; output
        remain = input.copy()
        output = QCircuit()
        while remain.size() != 0:
            gate = remain.gates[0]
            if gate.name == "CX":
                nxt = next_gate(remain, 0)
                g = remain.gates[nxt]
                if g.name == "CX" and g.qubits == gate.qubits:
                    remain.delete(nxt)
                else:
                    output.append(gate)
            else:
                output.append(gate)
            remain.delete(0)
        return output
