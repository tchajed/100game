#!/usr/bin/env python3

from enum import Enum
from graphviz import Digraph


class Player(Enum):
    current = 1
    other = 2


class GameNode:
    def __init__(self, game_sum=0):
        self.game_sum = game_sum

    def actions(self):
        actions = []
        for i in range(1, 10+1):
            if i + self.game_sum > 100:
                continue
            actions.append(GameNode(self.game_sum + i))
        return actions

    def winner(self):
        if self.game_sum < 100:
            return None
        # you lose if on your turn you have no moves
        return Player.other

    def state(self):
        return self.game_sum


class GameTree:
    node_cache = {}

    def __init__(self, node, subtrees=None):
        self.node = node
        self._subtrees = subtrees
        self._winner = None

    def subtrees(self):
        for n in self.node.actions():
            if n.state() not in GameTree.node_cache:
                GameTree.node_cache[n.state()] = GameTree(n)
            yield GameTree.node_cache[n.state()]

    def _compute_winner(self):
        node_win = self.node.winner()
        if node_win is not None:
            return node_win
        for tree in self.subtrees():
            if tree.winner == Player.other:
                # tree_winner is us; we force a win
                return Player.current
            # this is a loss, skip it
        # everything was a loss
        return Player.other

    @property
    def winner(self):
        if self._winner is None:
            self._winner = self._compute_winner()
        return self._winner

    @classmethod
    def init(cls):
        return cls(GameNode())

    def node_ident(self):
        return "{}".format(100 - self.node.game_sum)

    def node_name(self):
        return self.node_ident()


def viz(tree):
    dot = Digraph(name="100 game tree",
                  node_attr={"style": "filled"})
    processed = {}
    trees = [tree]
    while trees:
        tree = trees.pop(0)
        if tree.node.state() in processed:
            continue
        if tree.winner == Player.current:
            attrs = {"fillcolor": "#b8fc88"}
        else:
            attrs = {"fillcolor": "#f72727",
                     "fontcolor": "#ffffff"}
        dot.node(tree.node_ident(), tree.node_name(), **attrs)
        for subtree in tree.subtrees():
            throwing_victory = (tree.winner == Player.current and
                                subtree.winner != Player.other)
            winning_move = (tree.winner == Player.current and
                            subtree.winner == Player.other)
            color = "black"
            if throwing_victory:
                color = "#d0d0d0"
            if winning_move:
                color = "blue"
            dot.edge(tree.node_ident(), subtree.node_ident(), color=color)
            trees.append(subtree)
        processed[tree.node.state()] = True
    return dot


if __name__ == "__main__":
    tree = GameTree.init()
    dot = viz(tree)
    dot.save("100game.dot")
