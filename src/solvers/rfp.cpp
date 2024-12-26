/*
 * Copyright 2024 Jeffrey Considine
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "rfp.hpp"

#ifdef RFP_TRACE
#include <iostream>
#endif
#include <queue>
#include <utility>

namespace pg {

struct EdgeHash
{
    std::size_t operator()(const std::pair<int, int>& p) const noexcept
    {
        int v = std::get<0>(p);
        int s = std::get<1>(p);
        return std::hash<int>{}(v) ^ std::hash<int>{}(s);
    }
};

RFPSolver::RFPSolver(Oink& oink, Game& game) : Solver(oink, game)
{
}

void
RFPSolver::run()
{
    game.compress();

#ifdef RFP_TRACE
    std::cerr << "#############################################################" << std::endl;
    std::cerr << "COMPRESSED GRAPH" << std::endl;
    for(int v = 0; v < nodecount(); ++v)
    {
        const int *to_v = outs(v);
        std::cerr << v << " " << priority(v) << " " << owner(v) << " " << *to_v;

        for(++to_v; *to_v >= 0; ++to_v)
        {
            std::cerr << "," << *to_v;
        }

        std::cerr << std::endl;
    }
#endif

    for(int target_priority = priority(nodecount() - 1);
        target_priority >= priority(0);
        --target_priority)
    {
#ifdef RFP_TRACE
        std::cerr << "TARGET PRIORITY " << target_priority << std::endl;
#endif
        int winner = target_priority % 2;

        std::unordered_set<int> target_vertices;
        for(int v = 0; v < nodecount(); ++v)
        {
            if((priority(v) >= target_priority) &&
                (priority(v) % 2 == winner) &&
                (!game.isSolved(v)))
            {
                target_vertices.insert(v);
            }
        }
        if(!target_vertices.size())
        {
            // all relevant vertices are covered by higher priority strategies
            continue;
        }

        std::unordered_map<int,int> target_strategy = solve_infinite(winner, target_vertices);
        for(const auto& strategy_entry : target_strategy)
        {
            int v = strategy_entry.first;
            if(!game.isSolved(v))
            {
#ifdef RFP_TRACE
                std::cerr << "SAVING SOLUTION " << v << " " << winner << " " << strategy_entry.second << std::endl;
#endif
                game.solve(v, winner, strategy_entry.second);
            }
        }
    }

#ifdef RFP_TRACE
    std::cerr << "FINAL OUTPUT:";
    for(int v = 0; v < nodecount(); ++v)
    {
        assert(game.isSolved(v));
        std::cerr << " " << v << "=" << game.getStrategy(v);
    }
    std::cerr << std::endl;
#endif
}

std::unordered_map<int, int> RFPSolver::solve_infinite(int winner, const std::unordered_set<int>& target_vertices)
{
    assert(target_vertices.size() > 0);

#ifdef RFP_TRACE
    std::cerr << "  SOLVE INFINITE " << winner << ": ";
    for(int i : target_vertices)
    {
        std::cerr << i << " ";
    }
    std::cerr << std::endl;
#endif

    std::unordered_set<int> current_vertices(target_vertices);
    std::unordered_map current_strategy = solve_once(winner, current_vertices);
    while(true)
    {
        // construct set of vertices that could force path to target once.
        std::unordered_set<int> next_vertices;
        for(int v : current_vertices)
        {
            auto search = current_strategy.find(v);
            if(search != current_strategy.end())
            {
                next_vertices.insert(v);
            }
        }

        // if all the current vertices can force a path, then we are done.
        if(next_vertices.size() == current_vertices.size())
        {
            break;
        }

        current_vertices = next_vertices;
        current_strategy = solve_once(winner, current_vertices);
    }

#ifdef RFP_TRACE
    std::cerr << "  SOLVE INFINITE OUTPUT:";
    for(auto vs : current_strategy)
    {
        std::cerr << " " << std::get<0>(vs) << "=" << std::get<1>(vs);
    }
    std::cerr << std::endl;
#endif

    return current_strategy;
}

std::unordered_map<int, int> RFPSolver::solve_once(int winner, const std::unordered_set<int>& target_vertices)
{
#ifdef RFP_TRACE
    std::cerr << "    SOLVE ONCE " << winner << ": ";
    for(int i : target_vertices)
    {
        std::cerr << i << " ";
    }
    std::cerr << std::endl;
#endif

    std::unordered_map<int, int> output;

    // these edges are confirmed to allow the designated winner to guarantee
    // the target vertices will be visited.

    std::unordered_set<std::pair<int, int>, EdgeHash> winning_edges;

    // track number of remaining outgoing edges for each vertex.
    // if these run out without finding a winning strategy, the vertex is a loss.
    std::vector<int> remaining_edges(nodecount());
    for(int v = 0; v < nodecount(); ++v)
    {
        remaining_edges[v] = 0;
        for(const int *to_v = outs(v); *to_v >= 0; ++to_v)
        {
            // only count edges to unsolved vertices.
            if(!game.isSolved(*to_v))
            {
                ++remaining_edges[v];
            }
        }
#ifdef RFP_TRACE
        std::cerr << "      REMAINING[" << v << "] = " << remaining_edges[v] << std::endl;
#endif
    }

    // retrograde queue of new strategy entries to process.
    std::queue<std::pair<int, int>> winning_edges_todo;

    auto enqueue = [&](int v, int s)
    {
#ifdef RFP_TRACE
        std::cerr << "        QUEUE " << v << " " << s << std::endl;
#endif
        winning_edges_todo.emplace(v, s);
    };

    auto set_strategy = [&](int v, int s)
    {
        assert(output.find(v) == output.end());

#ifdef RFP_TRACE
        std::cerr <<  "        STRATEGY " << v << " " << s << std::endl;
#endif
        output[v] = s;

        if(target_vertices.find(v) != target_vertices.end())
        {
            return;
        }

        for(const int *from_v = ins(v); *from_v >= 0; ++from_v)
        {
            enqueue(*from_v, v);
        }
    };

#ifdef RFP_TRACE
    std::cerr << "      INITIAL QUEUE" << std::endl;
#endif

    // seed queue with nodes that can move to the target vertices
    for(int v : target_vertices)
    {
        for(const int *from_v = ins(v); *from_v >= 0; ++from_v)
        {
            enqueue(*from_v, v);
        }
    }

    // process queue

    while(winning_edges_todo.size())
    {
        // the first part of this loop runs once per edge.

        std::pair<int, int> winning_edge = winning_edges_todo.front();
        winning_edges_todo.pop();

        int v = std::get<0>(winning_edge);
        int strategy = std::get<1>(winning_edge);

#ifdef RFP_TRACE
        std::cerr << "      PROCESS " << v << " " << strategy << std::endl;
#endif

        if(game.isSolved(strategy))
        {
            // this is an edge leading to a previously solved priority
#ifdef RFP_TRACE
            std::cerr << "        ALREADY SOLVED STRATEGY " << strategy << std::endl;
#endif
            continue;
        }

        auto search = output.find(v);
        if(search != output.end())
        {
            // already know how to win from this vertex.
#ifdef RFP_TRACE
            std::cerr << "        ALREADY SOLVED VERTEX " << v << std::endl;
#endif
            continue;
        }

        if(winning_edges.find(winning_edge) != winning_edges.end())
        {
            // already processed this edge
#ifdef RFP_TRACE
            std::cerr << "        ALREADY PROCESSED EDGE " << v << " " << strategy << std::endl;
#endif
            continue;
        }

        // the rest of this loop runs at most once per edge.

        winning_edges.insert(winning_edge);

        if(owner(v) == winner)
        {
            // new winning vertex. this block runs at most once per vertex.
#ifdef RFP_TRACE
            std::cerr << "        NEW WINNER " << v << std::endl;
#endif
            output[v] = strategy;

            for(const int *from_v = ins(v); *from_v >= 0; ++from_v)
            {
                enqueue(*from_v, v);
            }

            continue;
        }
        else
        {
            // possible losing vertex. this block can run at most once per edge.

#ifdef RFP_TRACE
            std::cerr << "        MAYBE LOSER " << v << std::endl;
#endif
            assert(remaining_edges[v] > 0);
            --remaining_edges[v];
#ifdef RFP_TRACE
            std::cerr << "        REMAINDER[" << v << "] = " << remaining_edges[v] << std::endl;
#endif
            if(remaining_edges[v] == 0)
            {
                // new losing vertex. this block can run at most once per vertex.

#ifdef RFP_TRACE
                std::cerr << "        NEW LOSER " << v << std::endl;
#endif
                output[v] = -1;

                for(const int *from_v = ins(v); *from_v >= 0; ++from_v)
                {
                    // this block can run at most once per edge.
                    enqueue(*from_v, v);
                }
            }            
        }
    }

    // done

#ifdef RFP_TRACE
    std::cerr << "    SOLVE ONCE OUTPUT:";
    for(auto vs : output)
    {
        std::cerr << " " << std::get<0>(vs) << "=" << std::get<1>(vs);
    }
    std::cerr << std::endl;
#endif
    return output;
}

}
