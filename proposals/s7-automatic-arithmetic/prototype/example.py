"""Compile and evaluate the least power of two strictly above a large input."""
from formula import And, le, pow2, least_graph
from producer import Compiler, extract_witness
from checker import verify, check_witness


def main() -> None:
    relation = And(pow2('y'), le({'x': 1, 'y': -1}, -1))
    graph = least_graph(relation, 'y', 'z')
    query = {'context': ['x', 'y'], 'formula': graph}
    certificate = Compiler().bundle(graph, query['context'])
    verify(certificate, query)
    machine = certificate['nodes'][certificate['root']]['dfa']
    inputs = [10**100 + 37]
    record = extract_witness(machine, inputs)
    if record is None:
        raise RuntimeError('expected a witness for this total relation')
    check_witness(machine, inputs, record)
    print('input:', inputs[0])
    print('least witness:', record['witness'])
    print('states:', len(machine['trans']))
    print('scope: checked by the Python replay implementation, not by Lean')


if __name__ == '__main__':
    main()
