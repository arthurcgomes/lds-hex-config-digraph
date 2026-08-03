/*
 * Companion code for "Optimal and Quasi-Optimal Locating-Dominating Sets
 * in Infinite Hexagonal Strips" (Arthur C. Gomes and Yoshiko Wakabayashi).
 *
 * Builds the configuration digraph used to compute the minimum density of
 * a locating-dominating set (LDS) on the infinite hexagonal strip H_k.
 *
 * Each barcode of a 4-bar becomes a vertex of a configuration digraph; an arc
 * u -> v exists iff the last two columns of u equal the first two columns
 * of v AND the resulting overlapping 6-bar is a barcode. 
 * Arc weights count the number of code vertices in the last two columns of barcode
 * v in the arc u -> v. 
 * The minimum mean cycle (via Howard's algorithm) of this digraph gives the 
 * minimum density of an LDS on H_k.
 *
 * Build: g++ -std=c++17 -O3 -pthread config_digraph_mmc.cpp -o config_digraph_mmc 
 *   -I/path/to/lemon/include -L/path/to/lemon/lib -lemon
 *
 * Usage: ./config_digraph_mmc <grid_height>
 * Output: min_mean_cycle.txt containing the MMC value, cycle, and running time.
 *
 * Dependencies: LEMON graph library (https://lemon.cs.elte.hu)
 */


#include <iostream>
#include <vector>
#include <set>
#include <string>
#include <lemon/smart_graph.h>
#include <lemon/howard_mmc.h>
#include <lemon/path.h>
#include <ctime>
#include <fstream>
#include <thread>
#include <mutex>
#include <cmath>
#include <chrono>

using namespace std;

mutex arcs_mutex;

// Global variables
lemon::SmartDigraph config_digraph;
// Maps a digraph vertex to its barcode.
lemon::SmartDigraph::NodeMap<vector<char> > vertex_bar_map(config_digraph);
// Same data as vertex_bar_map, but stored in a vector so that create_arcs 
// can split vertices into contiguous ranges across threads.
vector<pair<lemon::SmartDigraph::Node, vector<char> > > indexed_vertices;
lemon::SmartDigraph::ArcMap<int> arc_weight(config_digraph);
int grid_height;

constexpr int BAR_WIDTH = 4;
constexpr int SIX_BAR_WIDTH = 6;


// Bitmasks to get the neighbours as bitstrings
constexpr char neighbours_same_line_col_1 = 40;    // 00 101000
constexpr char neighbours_same_line_col_2 = 20;    // 00 010100
constexpr char neighbours_same_line_col_3 = 10;    // 00 001010
constexpr char neighbours_same_line_col_4 = 5;     // 00 000101

constexpr char neighbours_other_line_col_1 = 16;   // 00 010000
constexpr char neighbours_other_line_col_2 = 8;    // 00 001000
constexpr char neighbours_other_line_col_3 = 4;    // 00 000100
constexpr char neighbours_other_line_col_4 = 2;    // 00 000010


/*
 * Returns 1 if bit in position (row, col) is 1.
 */
static inline int get_bit(char row_bits, int col, int width)
{
    return (row_bits >> (width - 1 - col)) % 2;
}

/*
 * Prints a graphical representation of a 4-bar (or 6-bar) code to 'out' 
 * (stdout as default), showing which vertices are in the LDS.
 */
void print_bar(const vector<char>& code, const int width, ostream& out = std::cout)
{
    int height = code.size();

    for (int i = 0; i < height; i++) {
        for (int j = 0; j < width; j++) {
            out << get_bit(code[i], j, width);
            if (j < width - 1) out << "--";
            else out << '\n';
        }
        if (i < height - 1) {
            for (int j = 0; j < width; j++) {
                if (i % 2 == 0) {
                    if (j % 2) out << "|  ";
                    else out << "   ";
                }
                else {
                    if (j % 2) out << "   ";
                    else out << "|  ";
                }
            }
            out << '\n';
        }
    }
}


/*
 * Returns the set of neighbours of vertex (row, col) that belong to the LDS
 * restricted to the given 4-bar (or 6-bar).
 */
set<pair<int, int> > neighbourhood_bar_in_code(const int row, const int col, 
        const int width, vector<char>& code)
{
    set<pair<int, int> > neighbours;

    // If row is even, then the even columns vertices have a neighbour in the 
    // column above and the odd column vertices have a neighbour in the column below.
    if (!(row % 2)) {
        if (!(col % 2) && row != 0 && get_bit(code[row-1], col, width)) {
            neighbours.insert(make_pair(row - 1, col));
        } 
        else if ((col % 2) && row != grid_height - 1 && get_bit(code[row+1], col, width)) {
            neighbours.insert(make_pair(row + 1, col));
        }
    }
    // If row is odd, then the even columns vertices have a neighbour in the 
    // column below and the odd column vertices have a neighbour in the column above.
    else {
        if (!(col % 2) && row != grid_height - 1 && get_bit(code[row+1], col, width)) {
            neighbours.insert(make_pair(row + 1, col));
        } 
        else if (col % 2 && get_bit(code[row-1], col, width)) {
            neighbours.insert(make_pair(row - 1, col));
        }
    }

    // Adds the neighbours that are in the same row as the vertex
    if (col != 0 && get_bit(code[row], col - 1, width)) {
        neighbours.insert(make_pair(row, col - 1));
    }
    if (col != width - 1 && get_bit(code[row], col + 1, width)) {
        neighbours.insert(make_pair(row, col + 1));
    }

    return neighbours;
} 


/*
 * Checks whether `code` is a valid barcode. To do that it verifies that, for every
 * vertex that is not in the set in the two middle columns it:
 *   (1) has at least one neighbour in the set (domination);
 *   (2) that neighbourhood in the set is unique among the vertices in the two
 *       middle columns (locating property).
 */
bool is_barcode(vector<char>& code)
{
    // First, check if for each vertex u not in the code and in the two middle
    // columns, N[u] \cap code is not empty.
    for (int i = 0; i < grid_height; i++) {
        // column 1
        if (!get_bit(code[i], 1, BAR_WIDTH)) {
            set<pair<int, int> > neighbours = neighbourhood_bar_in_code(i, 1, BAR_WIDTH, code);
            if (neighbours.empty()) {
                return false;
            }
        }

        // column 2
        if (!get_bit(code[i], 2, BAR_WIDTH)) {
            set<pair<int, int> > neighbours = neighbourhood_bar_in_code(i, 2, BAR_WIDTH, code);
            if (neighbours.empty()) {
                return false;
            }
        }
    }

    // Second, check if for each pair of vertices u, v not in the code and in the
    // two middle columns, N[u] \cap code != N[v] \cap code

    for (int i = 0; i < grid_height - 1; i++) {
        set<pair<int, int> > neighbourhood_a, neighbourhood_b;

        // Compare pairs (i, 1) and (i + 1, 2) if neither is in the code
        if (!get_bit(code[i], 1, BAR_WIDTH) && !get_bit(code[i+1], 2, BAR_WIDTH)) {
            neighbourhood_a = neighbourhood_bar_in_code(i, 1, BAR_WIDTH, code);
            neighbourhood_b = neighbourhood_bar_in_code(i+1, 2, BAR_WIDTH, code);

            if (neighbourhood_a == neighbourhood_b) {
                return false;
            }
        }

        // Compare pairs (i, 2) and (i + 1, 1) if neither is in the code
        if (!get_bit(code[i], 2, BAR_WIDTH) && !get_bit(code[i+1], 1, BAR_WIDTH)) {
            neighbourhood_a = neighbourhood_bar_in_code(i, 2, BAR_WIDTH, code);
            neighbourhood_b = neighbourhood_bar_in_code(i+1, 1, BAR_WIDTH, code);

            if (neighbourhood_a == neighbourhood_b) {
                return false;
            }
        }
    } 

    return true;
}


/*
 * Recursively enumerates all 2^(BAR_WIDTH*grid_height) possible 4-bar codes.
 * Valid codes (barcodes), become vertices of the configuration digraph.
 */
void generate_all_possible_codes(vector<char>& code, int i=0)
{
    if (i == BAR_WIDTH*grid_height) {
        if (is_barcode(code)) {
            // Adds vertex that corresponds to this barcode in the configuration graph
            lemon::SmartDigraph::Node v = config_digraph.addNode();
            vertex_bar_map[v] = code;
            indexed_vertices.push_back({v, code});
        }

        return;
    } 

    int row = i/BAR_WIDTH;
    int col = i - BAR_WIDTH*row;

    code[row] = code[row] | (1 << ((BAR_WIDTH - 1) - col));
    generate_all_possible_codes(code, i + 1);
    code[row] = code[row] ^ (1 << ((BAR_WIDTH - 1) - col));
    generate_all_possible_codes(code, i + 1);
}


/*
 * Creates the vertices of the configuration digraph.
 */ 
void create_vertices()
{
    // Matrix used to generate all possible codes of a 4-bar
    vector<char> code(grid_height);

    // Actually generates the codes and adds the barcodes of vertices to the vertex_bar_map
    generate_all_possible_codes(code);
}


/*
 * Checks whether the 6-bar formed by overlapping the last two columns of bar_u
 * with the two first columns of bar_v is a valid barcode.
 *
 * This check decides whether there is an arc u -> v in the configuration digraph.
 */
bool is_valid_six_bar(const vector<char>& bar_u, const vector<char>& bar_v) {
    // creates the 6-bar code
    vector<char> six_bar(grid_height);
    for (int i = 0; i < grid_height; i++) {
        six_bar[i] = (bar_u[i] << 2) + (bar_v[i] % 4);
    }

    // checks if six_bar is a barcode
    for (int i = 0; i < grid_height - 1; i++) {
        if (i > 0 && i % 2 == 0) {
            // compare columns 1 and column 3
            if (!get_bit(six_bar[i], 1, SIX_BAR_WIDTH) && !get_bit(six_bar[i], 3, SIX_BAR_WIDTH) &&
                    ((six_bar[i] & neighbours_same_line_col_1) + (six_bar[i+1] & neighbours_other_line_col_1)) == 
                    ((six_bar[i] & neighbours_same_line_col_3) + (six_bar[i+1] & neighbours_other_line_col_3))) {
                return false;
            }
            // compare columns 2 and column 4
            if (!get_bit(six_bar[i], 2, SIX_BAR_WIDTH) && !get_bit(six_bar[i], 4, SIX_BAR_WIDTH) &&
                    ((six_bar[i] & neighbours_same_line_col_2) + (six_bar[i-1] & neighbours_other_line_col_2)) == 
                    ((six_bar[i] & neighbours_same_line_col_4) + (six_bar[i-1] & neighbours_other_line_col_4))) {
                return false;
            }
        }
        else if (i == 0) {
            // compare columns 1 and column 3
            if (!get_bit(six_bar[i], 1, SIX_BAR_WIDTH) && !get_bit(six_bar[i], 3, SIX_BAR_WIDTH) &&
                    ((six_bar[i] & neighbours_same_line_col_1) + (six_bar[i+1] & neighbours_other_line_col_1)) == 
                    ((six_bar[i] & neighbours_same_line_col_3) + (six_bar[i+1] & neighbours_other_line_col_3))) {
                return false;
            }
            // compare columns 2 and column 4
            if (!get_bit(six_bar[i], 2, SIX_BAR_WIDTH) && !get_bit(six_bar[i], 4, SIX_BAR_WIDTH) &&
                    ((six_bar[i] & neighbours_same_line_col_2) == (six_bar[i] & neighbours_same_line_col_4))) {
                return false;
            }

        }
        else {
           // compare columns 1 and column 3
            if (!get_bit(six_bar[i], 1, SIX_BAR_WIDTH) && !get_bit(six_bar[i], 3, SIX_BAR_WIDTH) &&
                    ((six_bar[i] & neighbours_same_line_col_1) + (six_bar[i-1] & neighbours_other_line_col_1)) == 
                    ((six_bar[i] & neighbours_same_line_col_3) + (six_bar[i-1] & neighbours_other_line_col_3))) {
                return false;
            }
            // compare columns 2 and column 4
            if (!get_bit(six_bar[i], 2, SIX_BAR_WIDTH) && !get_bit(six_bar[i], 4, SIX_BAR_WIDTH) &&
                    ((six_bar[i] & neighbours_same_line_col_2) + (six_bar[i+1] & neighbours_other_line_col_2)) == 
                    ((six_bar[i] & neighbours_same_line_col_4) + (six_bar[i+1] & neighbours_other_line_col_4))) {
                return false;
            } 
        }
        // compare columns 2 and 3
        if (!get_bit(six_bar[i], 2, SIX_BAR_WIDTH) && !get_bit(six_bar[i+1], 3, SIX_BAR_WIDTH) &&
                neighbourhood_bar_in_code(i, 2, SIX_BAR_WIDTH, six_bar) == neighbourhood_bar_in_code(i+1, 3, SIX_BAR_WIDTH, six_bar)) {
            return false;
        }
        // compare columns 3 and 2
        if (!get_bit(six_bar[i], 3, SIX_BAR_WIDTH) && !get_bit(six_bar[i+1], 2, SIX_BAR_WIDTH) &&
                neighbourhood_bar_in_code(i, 3, SIX_BAR_WIDTH, six_bar) == neighbourhood_bar_in_code(i+1, 2, SIX_BAR_WIDTH, six_bar)) {

            return false;
        }
    }

    // special case for the last row
    if ((grid_height - 1) % 2 == 0) {
        // compare column 1 and column 3
        if (!get_bit(six_bar[grid_height-1], 1, SIX_BAR_WIDTH) && !get_bit(six_bar[grid_height-1], 3, SIX_BAR_WIDTH) &&
                ((six_bar[grid_height - 1] & neighbours_same_line_col_1) == 
                (six_bar[grid_height - 1] & neighbours_same_line_col_3))) {
            return false;
        }
        // compare column 2 and column 4
        if (!get_bit(six_bar[grid_height-1], 2, SIX_BAR_WIDTH) && !get_bit(six_bar[grid_height-1], 4, SIX_BAR_WIDTH) &&
                ((six_bar[grid_height-1] & neighbours_same_line_col_2) + (six_bar[grid_height-2] & neighbours_other_line_col_2)) == 
                ((six_bar[grid_height-1] & neighbours_same_line_col_4) + (six_bar[grid_height-2] & neighbours_other_line_col_4))) {
            return false;
        }
    }
    else {
        // compare column 1 and column 3
        if (!get_bit(six_bar[grid_height-1], 1, SIX_BAR_WIDTH) && !get_bit(six_bar[grid_height-1], 3, SIX_BAR_WIDTH) &&
                ((six_bar[grid_height-1] & neighbours_same_line_col_1) + (six_bar[grid_height-2] & neighbours_other_line_col_1)) == 
                ((six_bar[grid_height-1] & neighbours_same_line_col_3) + (six_bar[grid_height-2] & neighbours_other_line_col_3))) {
            return false;
        }
        // compare column 2 and column 4
        if (!get_bit(six_bar[grid_height-1], 2, SIX_BAR_WIDTH) && !get_bit(six_bar[grid_height-1], 4, SIX_BAR_WIDTH) &&
                ((six_bar[grid_height-1] & neighbours_same_line_col_2)  == 
                (six_bar[grid_height-1] & neighbours_same_line_col_4))) {
            return false;
        } 
    }

    return true;
}


/*
 * Tests whether bar_source's last two columns match bar_targets's first two columns 
 * and the resulting 6-bar overlap is a valid barcode, adds arc vtx_source -> vtx_target
 * to the configuration digraph with weight equal to the number of code vertices 
 * in bar_target's first two columns.
 */
void try_add_arc(lemon::SmartDigraph::Node vtx_source, const vector<char>& bar_source,
                 lemon::SmartDigraph::Node vtx_target, const vector<char>& bar_target)
{
    bool overlap = true;
    int last_two_columns_weight = 0;

    for (int i = 0; i < grid_height; i++) {
        if (bar_source[i] % 4 != (bar_target[i] >> 2) % 4) {
            overlap = false;
            break;
        }
        if ((bar_target[i] >> 1) % 2) last_two_columns_weight += 1;
        if (bar_target[i] % 2) last_two_columns_weight += 1;
    }

    // check if the code of the 6-bar formed by the overlap of the 4-bars
    // is a barcode.
    if (!overlap || !is_valid_six_bar(bar_source, bar_target)) {
        return;
    }

    arcs_mutex.lock();
    lemon::SmartDigraph::Arc a = config_digraph.addArc(vtx_source, vtx_target);
    arc_weight[a] = last_two_columns_weight;
    arcs_mutex.unlock();
}


/*
 * Function for a single thread: compare pairs of vertices (u, v) such that
 * begin <= u < end and u <= v, and checks whether the arcs u -> v, v -> u, and
 * in the case u = v, u -> u, should be in the configuration digraph.
 */
void compare_vertices(int begin, int end)
{
    for (int u = begin; u < end; u++) {
        lemon::SmartDigraph::Node vtx_u = indexed_vertices[u].first;
        vector<char> bar_u = indexed_vertices[u].second;

        for (int v = u; v < indexed_vertices.size(); v++) {
            lemon::SmartDigraph::Node vtx_v = indexed_vertices[v].first;
            if (u == v) {
                try_add_arc(vtx_u, bar_u, vtx_u, bar_u);
            }
            else {
                vector<char> bar_v = indexed_vertices[v].second;
                try_add_arc(vtx_u, bar_u, vtx_v, bar_v);
                try_add_arc(vtx_v, bar_v, vtx_u, bar_u);
            }
        }
    }
}


/* Splits all pairs (u, v) into num_splits threads and calls compare_vertices 
 * on each block in parallel. The blocks are chosen so that each thread has 
 * roughly the same amount of work.
 */
void create_arcs()
{

    vector<thread> threads;
    int num_splits = thread::hardware_concurrency();
    unsigned long long num_vts = lemon::countNodes(config_digraph);

    unsigned long long begin = 0;

    for (int i = num_splits - 1; i >= 0; i--) {
        unsigned long long end = (-1 + sqrt(1 + 4*i*num_vts*(num_vts + 1) / num_splits)) / 2;
        cout << "Thread " << i << ": vertices [" << begin << ", " << num_vts - end << ")\n";
        threads.emplace_back(thread(compare_vertices, begin, num_vts - end));
        begin = num_vts - end;
    }

    for (auto& th : threads) {
        th.join();
    }
}


/*
 * Builds the full configuration digraph.
 */
void build_digraph()
{
    create_vertices();

    cout << "Number of vertices: " << lemon::countNodes(config_digraph) << endl;

    create_arcs();
}


int main(int argc, char* argv[])
{
    if (argc != 2) {
        cerr << "Usage: ./config_digraph_mmc <grid_height>\n";
        return 1;
    }


    // Height of the hexagonal grid
    grid_height = stoi(argv[1]);

    clock_t start_time_clock, end_time_clock, end_digraph_build_clock;
    chrono::time_point<chrono::system_clock> start_time, end_time, end_digraph_build;

    start_time_clock = clock();
    start_time = chrono::system_clock::now();


    build_digraph();

    end_digraph_build_clock = clock();
    end_digraph_build = chrono::system_clock::now();

    cout << "Configuration digraph was built!\n";

    lemon::HowardMmc<lemon::SmartDigraph, lemon::SmartDigraph::ArcMap<int> > mmc(config_digraph, arc_weight);

    mmc.run();
    end_time_clock = clock();
    end_time = chrono::system_clock::now();

    double mean = mmc.cycleMean();
    lemon::Path<lemon::SmartDigraph> cycle = mmc.cycle();

    ofstream file("min_mean_cycle.txt");

    if (file.is_open()) {
        file << "Number of vertices: " << lemon::countNodes(config_digraph) << endl;
        file << "Number of arcs: " << lemon::countArcs(config_digraph) << endl << endl;

        file << "mmc: " << mean << endl;

        file << "CYCLE\n";

        for (int i = 0; i < cycle.length(); i++) {
            lemon::SmartDigraph::Arc a = cycle.nth(i);
            file << "(" << config_digraph.id(config_digraph.source(a))  << ", " << 
                config_digraph.id(config_digraph.target(a))  << "), : " << arc_weight[a] << endl;
            print_bar(vertex_bar_map[config_digraph.source(a)], BAR_WIDTH, file);
        }
        file << "\n\n";

        double total_time_clock = ((double)(end_time_clock - start_time_clock)) / CLOCKS_PER_SEC;
        double digraph_build_time_clock = ((double)(end_digraph_build_clock - start_time_clock)) / CLOCKS_PER_SEC;
        double mmc_time_clock = ((double)(end_time_clock - end_digraph_build_clock)) / CLOCKS_PER_SEC;

        chrono::duration<double> total_time = end_time - start_time;
        chrono::duration<double> digraph_build_time = end_digraph_build - start_time;
        chrono::duration<double> mmc_time = end_time - end_digraph_build;

        file << "CPU Time:\n";
        file << "Time to build configuration digraph: " << digraph_build_time_clock << "s\n";
        file << "Time to calculate MMC: " << mmc_time_clock << "s\n";
        file << "Total execution time: " << total_time_clock << "s\n";

        file << "User Time:\n";
        file << "Time to build configuration digraph: " << digraph_build_time.count() << "s\n";
        file << "Time to calculate MMC: " << mmc_time.count() << "s\n";
        file << "Total execution time: " << total_time.count() << "s\n";
    }

    file.close();

    return 0;
}
