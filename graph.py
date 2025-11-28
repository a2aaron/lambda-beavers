import csv
import argparse
import matplotlib.pyplot as plt
import subprocess
import io
import os

ALIVE_NODES = "Alive Nodes"
GARBAGE_NODES = "Garbage Nodes"


# Read the CSV and extract two columns of data
def read_csv(csv_reader: csv.DictReader):
    alive_nodes = []
    garbage_nodes = []
    for row in csv_reader:
        num_alive_nodes = int(row[ALIVE_NODES])
        num_garbage_nodes = int(row[GARBAGE_NODES])
        alive_nodes.append(num_alive_nodes)
        garbage_nodes.append(num_garbage_nodes)
    return alive_nodes, garbage_nodes


def save_plot(filename, alive_nodes, garbage_nodes):
    # Plot the extracted data as a stacked area chart
    plt.stackplot(
        range(len(alive_nodes)),
        alive_nodes,
        garbage_nodes,
        labels=[ALIVE_NODES, GARBAGE_NODES],
        colors=["#4CAF50", "#B0ACAC"],
    )
    plt.legend(loc="upper left")

    directory = os.path.dirname(filename)
    if not os.path.exists(directory):
        os.makedirs(directory)
    plt.savefig(filename)


def run(testnum: int, gc_ratio: float | None, period: int) -> str:
    args = [
        "cargo",
        "run",
        "--release",
        "--bin",
        "stats",
        "--",
        str(testnum),
        "--period",
        str(period),
    ]
    if gc_ratio is not None:
        args.append("--gc-ratio")
        args.append(str(gc_ratio))

    result = subprocess.run(
        args,
        stdout=subprocess.PIPE,
    )
    return result.stdout.decode("utf-8")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Convert a CSV file to a chart")
    parser.add_argument("testnum")
    parser.add_argument("--period", default=1)
    parser.add_argument("--gc_ratio")
    args = parser.parse_args()

    testnum = args.testnum
    period = args.period
    gc_ratio = args.gc_ratio

    csv_data = run(testnum, gc_ratio, period)

    csv_reader = csv.DictReader(io.StringIO(csv_data), delimiter=",")
    alive_nodes, garbage_nodes = read_csv(csv_reader)

    # Save the plot to a file
    filename = None
    if gc_ratio is None:
        filename = f"graphs/stats_{testnum}_no_gc.png"
    else:
        filename = f"graphs/stats_{testnum}_gc_{gc_ratio}.png"

    save_plot(filename, alive_nodes, garbage_nodes)
