lambda="(\ (\ 2) 1) (5 6)"
cargo run --release --bin graphviz2 -- "$lambda" --reductions 0 --no-garbage; dot -Tpng out.dot > out_0.png
cargo run --release --bin graphviz2 -- "$lambda" --reductions 1 --no-garbage; dot -Tpng out.dot > out_1.png
cargo run --release --bin graphviz2 -- "$lambda" --reductions 2 --no-garbage; dot -Tpng out.dot > out_2.png
cargo run --release --bin graphviz2 -- "$lambda" --reductions 3 --no-garbage; dot -Tpng out.dot > out_3.png
cargo run --release --bin graphviz2 -- "$lambda" --reductions 4 --no-garbage; dot -Tpng out.dot > out_4.png