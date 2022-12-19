/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.solver;

import fj.test.Bool;
import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.util.collection.HybridArrayHashSet;
import soot.dava.internal.SET.SETNode;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.*;

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {
    public int count_infact_not_change = 0;
    public int count_all = 0;
//    public Map<Node, Boolean> checkNodeMap = new HashMap();

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    public void DFS(CFG<Node> cfg) {//遍历每一个顶点，如果顶点没有被访问过，则让它进入DFSTraversal方法。
        HashMap<Node,Boolean> visited = new HashMap();
        for(Node node:cfg){
            visited.put(node,false);
        }
        for(Node node:cfg){
            if (!visited.get(node)) {
                DFSTraversal(node,visited,cfg);
            }
        }
    }
    public void printIndexLinenum(Node node) {
        try {
            Method getIndex = node.getClass().getDeclaredMethod("getIndex");
            Method getLineNumber = node.getClass().getDeclaredMethod("getLineNumber");
            System.out.println("index:"+getIndex.invoke(node)+";lineNumber:"+getLineNumber.invoke(node));
        } catch (Exception e) {
            System.out.println("error index,linenumber");
        }
    }
    public void DFSTraversal(Node node,HashMap<Node,Boolean> visited,CFG<Node> cfg) {//DFS核心代码
        if(visited.get(node)) return;
        visited.put(node,true);
        System.out.println("------");
        printIndexLinenum(node);
        System.out.println(node+" [->] ");
        for(Node n:cfg.getSuccsOf(node)){
            printIndexLinenum(n);
            System.out.println("\t"+n);
        }
    }
    protected boolean checkNodeSet(Set<Node> nodeset, HashMap<Node, Boolean> checkNodeMap) {
        for (Node node : nodeset) {
            Boolean flag = checkNodeMap.get(node);
            if (flag == null || !flag) {
                return false;
            }
        }
        return true;
    }

    protected void compute(CFG<Node> cfg, DataflowResult<Node, Fact> result, Node node) {
        Fact out = result.getOutFact(node);
        Fact in = result.getInFact(node);
        for (Node succsnode : cfg.getSuccsOf(node)) {
            Fact succsnode_in = result.getInFact(succsnode);
            this.analysis.meetInto(succsnode_in, out);//遍历节点后继s的in合并得到out(b)
        }
        //更新out//有meetinto,这里没必要
//        result.setOutFact(node, out);
        //use b//这里没有用bb,stmt可以直接判断 -def +uses
        //change判断结束怎么实现???
        count_all += 1;
        if (!this.analysis.transferNode(node, in, out)) {
            count_infact_not_change += 1;
        }//当前节点outfact->infact
        //更新in//有transferNode,这里没必要
//        result.setInFact(node, in);
    }

    //递归
//    protected void traversingBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result,Node nodetmp) {
    protected Set<Node> traversingBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result, Set<Node> nodeTmpSet, HashMap checkNodeMap) {
        //遍历前驱的后继是否可用，可用则取出计算并加入新的前驱节点，不可用则保留
        Set<Node> newnodeset = new HashSet();
        //nodeTmpSet前驱集合
        for (Node nodetmp : nodeTmpSet) {
            Set<Node> nodeset = cfg.getSuccsOf(nodetmp);
            //检查后继是否可用
            if (!checkNodeSet(nodeset, checkNodeMap)) {
                newnodeset.add(nodetmp);//不可用则保留
            } else {
                compute(cfg, result, nodetmp);//计算
                System.out.println("[]nodetmp:" + nodetmp);
                checkNodeMap.put(nodetmp, true);
                newnodeset.addAll(cfg.getPredsOf(nodetmp));//加入新的前驱节点
            }
        }
        return newnodeset;
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        System.out.println("doSolveBackward");
//        cfgshow(cfg);
        DFS(cfg);
//        Node nodetmp = cfg.getExit();
//        HashMap checkNodeMap = new HashMap();
//        checkNodeMap.put(nodetmp, true);
//        Set<Node> nodetmpset = cfg.getPredsOf(nodetmp);
//        //宽度遍历1次
//        while (nodetmpset.size() != 0) {
//            nodetmpset = traversingBackward(cfg, result, nodetmpset, checkNodeMap);
//        }
    }
}
