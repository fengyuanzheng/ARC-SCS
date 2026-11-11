#!/usr/bin/env python3
"""Check the CLI and exact results using temporary, generated graphs."""
import argparse
import itertools
from pathlib import Path
import random
import re
import struct
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


def binary_rows(rows):
    values = [4, len(rows), sum(map(len, rows))]
    values += list(map(len, rows))
    values += [v for row in rows for v in row]
    return struct.pack('=' + 'I' * len(values), *values)


def adjacency(n, edges):
    rows = [set() for _ in range(n)]
    for u, v in edges:
        rows[u].add(v)
        rows[v].add(u)
    return [sorted(row) for row in rows]


def optimum(rows, query, lower, upper):
    """Enumerate connected vertex subsets independently of the solver."""
    best = -1
    n = len(rows)
    for size in range(lower, min(upper, n) + 1):
        others = [v for v in range(n) if v != query]
        for subset in itertools.combinations(others, size - 1):
            selected = set(subset) | {query}
            reached = {query}
            pending = [query]
            for u in pending:
                for v in rows[u]:
                    if v in selected and v not in reached:
                        reached.add(v)
                        pending.append(v)
            if reached == selected:
                best = max(best, min(len(set(rows[v]) & selected)
                                     for v in selected))
    return best


class SmokeChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='arc-scs-check-')
        cls.addClassCleanup(cls.temp.cleanup)
        cls.directory = Path(cls.temp.name)
        rng = random.Random(4701)
        fixtures = [
            ('clique', adjacency(7, itertools.combinations(range(7), 2))),
            ('path', adjacency(8, [(v, v + 1) for v in range(7)])),
            ('disconnected', adjacency(8, [(v, v + 1)
                                          for v in (0, 1, 2, 4, 5, 6)])),
            ('edgeless', adjacency(5, [])),
        ]
        for i, probability in enumerate((0.2, 0.45, 0.7)):
            fixtures.append(('random' + str(i), adjacency(9, [
                (u, v) for u in range(9) for v in range(u + 1, 9)
                if rng.random() < probability])))
        fixtures.append(('branching', [
            [1, 2, 3, 5, 6, 10], [0, 3, 4, 8, 9, 10],
            [0, 3, 4, 7, 9, 10, 11], [0, 1, 2, 6, 8, 9, 10],
            [1, 2, 5, 7, 8, 9, 11], [0, 4, 7, 9, 10, 11],
            [0, 3, 7, 8, 10], [2, 4, 5, 6, 8, 9, 10],
            [1, 3, 4, 6, 7, 10, 11], [1, 2, 3, 4, 5, 7, 11],
            [0, 1, 2, 3, 5, 6, 7, 8, 11], [2, 4, 5, 8, 9, 10],
        ]))
        cls.graphs = []
        for name, rows in fixtures:
            path = cls.directory / (name + '.bin')
            path.write_bytes(binary_rows(rows))
            cls.graphs.append((name, path, rows))

    def invoke(self, executable, arguments, expected=0):
        result = subprocess.run([str(executable), *map(str, arguments)],
                                capture_output=True, text=True, timeout=20)
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, expected, output)
        self.assertNotIn('ERROR: AddressSanitizer', output)
        self.assertNotIn('runtime error:', output)
        return output

    def query(self, path, rows, query, lower, upper, extra=()):
        output = self.invoke(EXECUTABLE, ['-g', path, '-q', query, '-l', lower,
                                          '-u', upper, *extra])
        self.check_result(output, rows, query, lower, upper)
        return output

    def check_result(self, output, rows, query, lower, upper):
        best = optimum(rows, query, lower, upper)
        if best == -1:
            self.assertIn('[Status] NO_FEASIBLE', output)
            self.assertNotIn('[Status] SUCCESS', output)
            return
        result = re.search(r'\[Result\] status=OPTIMAL min_degree=(\d+) '
                           r'community_size=(\d+)', output)
        self.assertIsNotNone(result, output)
        self.assertEqual(int(result[1]), best, output)
        community = re.search(r'\[Community\] vertices:([^\n]*)', output)
        self.assertIsNotNone(community, output)
        vertices = list(map(int, re.findall(r'\d+', community[1])))
        selected = set(vertices)
        self.assertEqual(len(vertices), len(selected))
        self.assertEqual(len(vertices), int(result[2]))
        self.assertIn(query, selected)
        self.assertTrue(lower <= len(selected) <= upper)
        self.assertTrue(all(0 <= v < len(rows) for v in selected))
        self.assertEqual(min(len(set(rows[v]) & selected) for v in selected), best)
        reached = {query}
        pending = [query]
        for u in pending:
            for v in rows[u]:
                if v in selected and v not in reached:
                    reached.add(v)
                    pending.append(v)
        self.assertEqual(reached, selected)
        self.assertIn('[Status] SUCCESS', output)

    def test_exact_results(self):
        for name, path, rows in self.graphs:
            for query in (0, len(rows) - 1):
                for lower, upper in ((1, 3), (3, 6), (6, 9), (9, 12)):
                    with self.subTest(graph=name, query=query, bounds=(lower, upper)):
                        self.query(path, rows, query, lower, upper)

    def test_index_formats_and_batch(self):
        _, path, rows = self.graphs[-1]
        modes = [[], ['--core-only-index'], ['--core-peel-only-index'],
                 ['--core-threshold-bitmap-index'],
                 ['--hybrid-core-threshold-bitmap-index'],
                 ['--core-ordered-adjacency-index']]
        for i, flags in enumerate(modes):
            with self.subTest(format=flags):
                index = self.directory / ('index' + str(i) + '.idx')
                self.invoke(EXECUTABLE, ['-g', path, '--build-index',
                                        '--index-file', index, *flags])
                options = ['--use-index', '--index-file', index]
                if not flags:
                    options.append('--use-candidate-index')
                self.query(path, rows, 0, 3, 6, options)
                queries = self.directory / 'queries.txt'
                queries.write_text('# query vertices\n0\n\n8\n')
                output = self.invoke(EXECUTABLE, ['-g', path, '-l', 3, '-u', 6,
                                     '--batch-query-file', queries, *options])
                pieces = output.split('[Query] vertex=')[1:]
                self.assertEqual(len(pieces), 2, output)
                for query, piece in zip((0, 8), pieces):
                    self.check_result(piece, rows, query, 3, 6)

    def test_size_intervals(self):
        rows = adjacency(32, itertools.combinations(range(32), 2))
        path = self.directory / 'intervals.bin'
        path.write_bytes(binary_rows(rows))
        intervals = [(1, 1), (3, 6), (6, 9), (9, 12), (12, 15), (15, 18),
                     (3, 15), (6, 15), (9, 15), (15, 15), (3, 9), (3, 12),
                     (3, 18), (18, 20), (20, 22), (22, 24), (24, 26), (26, 28)]
        for lower, upper in intervals:
            with self.subTest(bounds=(lower, upper)):
                output = self.invoke(EXECUTABLE, ['-g', path, '-q', 0,
                                                  '-l', lower, '-u', upper])
                # In a complete graph, the optimum has upper vertices and
                # minimum degree upper-1; exhaustive enumeration is unnecessary.
                self.assertIn('status=OPTIMAL min_degree=' + str(upper - 1) +
                              ' community_size=' + str(upper), output)
                community = re.search(r'\[Community\] vertices:([^\n]*)', output)
                self.assertIsNotNone(community, output)
                vertices = list(map(int, re.findall(r'\d+', community[1])))
                self.assertEqual(len(vertices), upper)
                self.assertEqual(len(set(vertices)), upper)
                self.assertIn(0, vertices)
                self.assertTrue(all(0 <= v < 32 for v in vertices))

    def test_malformed_graphs(self):
        raw = lambda values: struct.pack('=' + 'I' * len(values), *values)
        malformed = {
            'empty': b'', 'short_header': raw([4, 3]),
            'wrong_width': raw([8, 0, 0]),
            'degree_sum': raw([4, 3, 0, 1, 0, 0]),
            'truncated_edges': raw([4, 3, 4, 1, 2, 1]),
            'endpoint': binary_rows([[9999], [0], []]),
            'self_loop': binary_rows([[0], [1]]),
            'duplicates': binary_rows([[1, 1], [0, 0], []]),
            'unsorted': binary_rows([[2, 1], [0], [0]]),
            'asymmetric': binary_rows([[1], [2], [3], [0]]),
            'odd_count': binary_rows([[1], []]),
            'oversized_count': raw([4, 0xffffffff, 0]),
            'trailing_bytes': binary_rows([[]]) + b'extra',
        }
        for name, content in malformed.items():
            with self.subTest(input=name):
                path = self.directory / ('invalid_' + name + '.bin')
                path.write_bytes(content)
                output = self.invoke(EXECUTABLE, ['-g', path, '-l', 1,
                                                  '-u', 3, '-q', 0], expected=1)
                self.assertNotIn('[Graph] status=READY', output)
                self.assertNotIn('[Status] SUCCESS', output)

    def test_cli_validation(self):
        _, path, _ = self.graphs[0]
        cases = [['-g', path, '-l', 6, '-u', 3, '-q', 0],
                 ['-g', path, '-l', 3, '-u', 6, '-q', 99],
                 ['-g', path, '-l', ' 3', '-u', 6, '-q', 0],
                 ['-g', path, '-l', 3, '-u', 6, '-q', 0,
                  '--use-candidate-index'], ['--unknown-option']]
        for arguments in cases:
            with self.subTest(arguments=arguments):
                self.invoke(EXECUTABLE, arguments, expected=1)
        help_text = self.invoke(EXECUTABLE, ['--help'])
        self.assertIn('--build-index', help_text)

    def test_graph_conversion(self):
        source = self.directory / 'edges.txt'
        target = self.directory / 'converted.bin'
        source.write_text('0 1\n1 0\n1 2\n2 2\n0 1\n')
        self.invoke(CONVERTER, ['--input', source, '--output', target,
                                '--vertices', 4])
        rows = adjacency(4, [(0, 1), (1, 2)])
        self.assertEqual(target.read_bytes(), binary_rows(rows))
        self.query(target, rows, 0, 1, 3)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exe', type=Path, default=ROOT / 'ARC_SCS')
    parser.add_argument('--graph-tool', type=Path, default=ROOT / 'tools/graph_tool')
    args = parser.parse_args()
    EXECUTABLE, CONVERTER = args.exe.resolve(), args.graph_tool.resolve()
    if not EXECUTABLE.is_file() or not CONVERTER.is_file():
        parser.error('build ARC_SCS and tools/graph_tool before running checks')
    unittest.main(argv=[__file__], verbosity=2)
