from circuit import QCircuit

class Faulty_CX_Cancellation:
    def run(self, input: QCircuit): # input = remain; output
        remain = input.copy()
        output = QCircuit()
        while remain.size() != 0:
            gate = remain.gates[0]
            if gate.name == "CX":
                remain.delete(0)
            else:
                output.append(gate)
            remain.delete(0)
        return output
