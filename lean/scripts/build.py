"""Build in dependency order so the large arithmetic proofs compile one at a time."""
from graphlib import TopologicalSorter
from pathlib import Path
import re
import subprocess


def main():
    root = Path(__file__).resolve().parents[1]
    paths = [root / "Turan.lean", *sorted((root / "Turan").rglob("*.lean"))]
    graph = {}
    for path in paths:
        name = ".".join(path.relative_to(root).with_suffix("").parts)
        imports = re.findall(r"^(?:public )?import\s+([^\n]+)", path.read_text(), re.M)
        graph[name] = sorted({word for line in imports for word in line.split()
                              if word.startswith("Turan.")})
    missing = set().union(*graph.values()) - graph.keys()
    if missing:
        raise ValueError(f"Missing local modules: {sorted(missing)}")
    order = list(TopologicalSorter(graph).static_order())
    for index, name in enumerate(order, 1):
        if index == 1 or index % 20 == 0:
            print(f"Building module {index} of {len(order)}", flush=True)
        subprocess.run(["lake", "-q", "build", f"+{name}:leanArts"], cwd=root, check=True)


if __name__ == "__main__":
    main()
