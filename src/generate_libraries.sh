for i in {0..19}; do
    mkdir -p results/P/SL/$i
    if [ -f results/P/SL/$i/14000000_generated.lean ]; then
        echo "SL $i already generated"
    else
        uv run python simple_loop.py --seed_file notions/P.lean --save_dir results/P/SL/$i 2> results/P/SL/$i/log3.txt &
    fi
    if [ -f results/P/CPL/$i/14000000_generated.lean ]; then
        echo "CPL $i already generated"
    else
        uv run python cmd_loop.py --seed_file notions/P.lean --save_dir results/P/CPL/$i --conjecture_model o3  2> results/P/CPL/$i/log3.txt &
    fi
done