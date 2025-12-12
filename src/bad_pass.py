from circuit import QCircuit
from utility import next_gate

class BadPass:
    def run(self, input: QCircuit):
        remain = input.copy()
        output = QCircuit()
        while remain.size() != 0:
            nxt = next_gate(remain, 0)
            remain.delete(nxt)
            remain.delete(0)
        return output
    