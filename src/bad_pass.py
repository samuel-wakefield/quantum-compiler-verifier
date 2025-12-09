from circuit import QCircuit

class BadPass:
    def run(self, input: QCircuit):
        remain = input.copy()
        output = QCircuit()
        while remain.size() != 0:
            gate = remain.gates[0]
            remain.delete(0)
        return output
    