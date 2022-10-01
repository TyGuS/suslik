import { EventEmitter } from 'events';
import arreq from 'array-equal';
import Vue from 'vue';
import 'vue-context/dist/css/vue-context.css';

import { VueEventHook } from './infra/event-hooks';

import './proof-trace.css';
import './menu.css';



class ProofTrace extends EventEmitter {

    id: string
    data: Data
    root: Data.NodeEntry

    nodeIndex: {
        byId: JSONMap<Data.NodeId, Data.NodeEntry>
        byGoalUid: JSONMap<Data.GoalId, Data.NodeEntry>
        childrenById: JSONMap<Data.NodeId, Data.NodeEntry[]>
        subtreeSizeById: JSONMap<Data.NodeId, number>
        statusById: JSONMap<Data.NodeId, Data.StatusEntry>
        derivationById: JSONMap<Data.NodeId, Data.DerivationTrailEntry>
        derivationByGoalUid: JSONMap<Data.GoalId, Data.DerivationTrailEntry>
        viewById: JSONMap<Data.NodeId, View.Node>
    }

    view: View.Props

    _actionHook = new VueEventHook('action')
    _dirty: {nodes: Set<Data.NodeEntry>} = {nodes: new Set}

    constructor(id: string, data: ProofTrace.Data, pane?: Vue & View.PaneProps) {
        super();
        this.id = id;
        this.data = data;
        this.root = this.data.nodes[0];

        this.createIndex();
        this.createView(pane);
    }

    append(data: Data, opts: {expand?: boolean} = {}) {
        Data.append(this.data, data);
        this.updateIndex(data);
        for (let node of data.nodes)
            this.addNode(node, opts);
        this.refreshView();
    }

    createIndex() {
        this.nodeIndex = {
            byId: new JSONMap, byGoalUid: new JSONMap,
            childrenById: new JSONMap, subtreeSizeById: new JSONMap,
            statusById: new JSONMap, derivationById: new JSONMap,
            derivationByGoalUid: new JSONMap,
            viewById: new JSONMap
        };
        this.updateIndex(this.data);
    }

    updateIndex(data: Data) {
        // Build byId, byGoalId
        for (let node of data.nodes) {
            this.nodeIndex.byId.set(node.id, node);
            if (node.goal)
                this.nodeIndex.byGoalUid.set(node.goal.uid, node);
        }

        // Build childrenById
        for (let node of data.nodes) {
            if (node.id.length >= 1) {
                var parent = node.id.slice(1);
                this.addChildToIndex(parent, node);
            }
        }

        let update = <T>(m: JSONMap<Data.NodeId, T>,
                         node: Data.NodeEntry, value: T) => {
            if (!node) return;
            var key = node.id, old = m.get(key);
            if (value !== old) { /** @todo better equality check */
                m.set(key, value);
                this._dirty.nodes.add(node);
            }
        }

        // Build statusById
        for (let entry of data.statuses) {
            var id = entry.at;
            update(this.nodeIndex.statusById,
                   this.nodeIndex.byId.get(id), entry);
        }

        // - compute transitive success
        // This has to be computed over *all* data; can optimize by only
        // considering ancestors of newly indexed nodes
        var nodesBottomUp = this.data.nodes.slice().sort((a, b) => b.id.length - a.id.length)
        for (let node of nodesBottomUp) {
            if (!this.nodeIndex.statusById.get(node.id)) {
                let children = (this.nodeIndex.childrenById.get(node.id) || [])
                                .map(c => this.nodeIndex.statusById.get(c.id));
                if (children.length) {
                    switch (node.tag) {
                    case Data.NodeType.OrNode:
                        if (children.some(x => x && x.status.tag === 'Succeeded'))
                            update(this.nodeIndex.statusById, node,
                                {at: node.id, status: {tag: 'Succeeded', from: '*'}});
                        break;
                    case Data.NodeType.AndNode:
                        if (children.length == node.nChildren &&
                            children.every(x => x && x.status.tag === 'Succeeded'))
                            update(this.nodeIndex.statusById,
                                node, {at: node.id, status: {tag: 'Succeeded', from: '*'}});
                        break;
                    }
                }
            }
        }

        // Build subtreeSizeById
        // (same here)
        var sz = this.nodeIndex.subtreeSizeById;
        for (let node of nodesBottomUp) {
            let children = (this.nodeIndex.childrenById.get(node.id) || []);
            update(sz, node, 1 + children.map(u => sz.get(u.id) || 1)
                                         .reduce((x,y) => x + y, 0));
        }

        // Build derivationById, derivationByGoalId
        for (let deriv of data.trail) {
            for (let goalUid of deriv.to) {
                this.nodeIndex.derivationByGoalUid.set(goalUid, deriv);
                let node = this.nodeIndex.byGoalUid.get(goalUid),
                    parent = node && this.parent(node);
                if (parent)
                    update(this.nodeIndex.derivationById, parent, deriv);
            }
        }

        for (let node of data.nodes) {
            if (node.goal) {
                var deriv = this.nodeIndex.derivationByGoalUid.get(node.goal.uid);
                if (deriv)
                    update(this.nodeIndex.derivationById, this.parent(node), deriv);
            }
        }
    }

    addChildToIndex(parent: Data.NodeId, child: Data.NodeEntry) {
        var m = this.nodeIndex.childrenById;
        // Note: nodes can re-occur if they were suspended during the search
        var l = m.get(parent) || [];
        if (!l.some(u => arreq(u.id, child.id)))
            m.set(parent, l.concat([child]));
    }

    parent(node: Data.NodeEntry) {
        var id = Data.parentId(node.id);
        return this.nodeIndex.byId.get(id);
    }

    children(node: Data.NodeEntry) {
        function lex2(a1: number[], a2: number[]) {
            let n = Math.min(2, a1.length, a2.length);
            for (let i = n - 1; i >= 0; i--) {
                if      (a1[i] < a2[i]) return -1;
                else if (a1[i] > a2[i]) return 1;
            }
            return 0;
        }
        function byId2(u1: Data.NodeEntry, u2: Data.NodeEntry) {
            return lex2(u1.id, u2.id);
        }
        return (this.nodeIndex.childrenById.get(node.id) || [])
            .sort(byId2); // modifies the list but that's ok
    }

    createView(pane: Vue & View.PaneProps) {
        this.view = {root: undefined};
        this._dirty.nodes.clear();
        if (this.root) {
            this.view.root = this.createNode(this.root);
            this.expandNode(this.view.root);
            if (this.view.root.children?.[0])  /* a bit arbitrary I know */
                this.expandNode(this.view.root.children[0]);
        }

        Vue.set(pane.docs, this.id, {trace: this.view});
        this._actionHook.attach(
            pane, (ev: View.ActionEvent) => this.viewAction(ev));
    }

    refreshView() {
        for (let node of this._dirty.nodes)
            this.refreshNode(node);
        this._dirty.nodes.clear();
    }

    destroy() {
        this._actionHook.detach();
    }

    addNode(node: Data.NodeEntry, opts: {expand?: boolean}) {
        if (node.id.length == 0) {  // this is the root
            this.root = node;
            this.view.root = this.createNode(node);
        }
        else {
            var parentId = Data.parentId(node.id),
                parentView = this.nodeIndex.viewById.get(parentId);
            if (parentView) {
                parentView.children ??= [];
                parentView.children.push(this.createNode(node));
                if (opts.expand) {   /** @todo only if parent is visible */
                    parentView.focus = true;
                    parentView.expanded = true;
                }
            }
        }
    }

    getStatus(node: Data.NodeEntry): Data.GoalStatusEntry { 
        var entry = this.nodeIndex.statusById.get(node.id);
        return entry && entry.status;
    }

    getSubtreeSize(node: Data.NodeEntry): number { 
        return this.nodeIndex.subtreeSizeById.get(node.id) || 1;
    }

    getDerivationTrail(node: Data.NodeEntry): Data.DerivationTrailEntry { 
        return this.nodeIndex.derivationById.get(node.id);
    }

    createNode(node: Data.NodeEntry): View.Node {
        var v = {value: node, children: undefined, focus: false, expanded: false,
                 status: this.getStatus(node),
                 derivation: this.getDerivationTrail(node),
                 numDescendants: this.getSubtreeSize(node)};
        this.nodeIndex.viewById.set(node.id, v);
        return v;
    }

    refreshNode(node: Data.NodeEntry) {
        var view = this.nodeIndex.viewById.get(node.id);
        if (view) {
            view.status = this.getStatus(node);
            view.derivation = this.getDerivationTrail(node);
            view.numDescendants = this.getSubtreeSize(node);
        }
    }

    expandNode(nodeView: View.Node, focus: boolean = false, emit: boolean = true) {
        nodeView.focus = focus;
        nodeView.expanded = true;
        nodeView.children = this.children(nodeView.value)
            .map(node => this.createNode(node));
        if (emit) this.emit('expand', nodeView);
    }

    expandOrNode(nodeView: View.Node, focus: boolean = false) {
        this.expandNode(nodeView, focus);
        for (let c of nodeView.children) {
            if (c.value.tag == Data.NodeType.AndNode) {
                this.expandNode(c, focus);
            }
        }
    }

    expandById(node: Data.NodeId, focus: boolean = false) {
        var view = this.nodeIndex.viewById.get(node);
        if (view) this.expandNode(view, focus);
    }

    expandByIds(nodes: Data.NodeId[]) {
        var sorted = nodes.slice().sort((a, b) => a.length - b.length);
        for (let node of sorted) this.expandById(node);
    }

    expandBranch(tip: Data.NodeId, focus: boolean = false) {
        var prefixes = tip.slice(1).map((_,i,u) => u.slice(-(i + 1)));
        for (let pfx of prefixes)
            this.expandById(pfx);
        // @todo focus tip
    }

    expandAll(nodeView: View.Node = this.view.root) {
        this.expandNode(nodeView, false, false);
        for (let c of nodeView.children)
            this.expandAll(c);
    }

    viewAction(ev: View.ActionEvent) {
        if (ev.id !== this.id) return;

        switch (ev.type) {
        case 'expand':
            this.expandOrNode(ev.target, true); break;
        case 'expandAll':
            this.expandAll(ev.target); break;
        case 'copyNodeId':
            this.copyJson(ev.target.value.id); break;
        }
    }

    copyJson(o: any) { 
        navigator.clipboard.writeText(JSON.stringify(o));
    }

}


namespace ProofTrace {

    export type Data = {
        nodes: Data.NodeEntry[],
        statuses: Data.StatusEntry[],
        trail: Data.DerivationTrailEntry[]
    };

    export namespace Data {

        export type NodeEntry = {
            id: NodeId
            tag: NodeType
            pp: string
            goal: GoalEntry
            nChildren: number
        };

        export type NodeId = number[];

        export enum NodeType { AndNode = 'AndNode', OrNode = 'OrNode' };
        const NODE_TAGS = Object.values(NodeType);

        export type GoalEntry = {
            id: GoalId
            uid: GoalUid
            pre: AssertionEntry, post: AssertionEntry, sketch: string,
            programVars:  [string, string][]
            existentials: [string, string][]
            ghosts:       [string, string][]
        };

        export type GoalId = string   /* this is actually the label */
        export type GoalUid = string

        export type AssertionEntry = {
            pp: String,
            phi: AST[],
            sigma: AST[]
        };

        export type AST = any /** @todo */

        export type Environment = Map<string, {type: string, of: string}>;

        export type StatusEntry = {
            at: NodeId
            status: GoalStatusEntry
        };

        export type GoalStatusEntry = {tag: "Succeeded" | "Failed", from?: string | string[]};

        export type DerivationTrailEntry = {
            tag: "DerivationTrail"
            from: GoalId
            to: GoalId[]
            ruleName: string
            subst: {[metavar: string]: OrVec<string>}
        };
        const DERIVATION_TRAIL_TAG = "DerivationTrail"

        export type OrVec<T> = T | T[];

        export function empty() {
            return {nodes: [], statuses: [], trail: []};
        }

        export function append(to: Data, from: Data): Data {
            to.nodes.push(...from.nodes);
            to.statuses.push(...from.statuses);
            to.trail.push(...from.trail);
            return to;
        }

        export function parse(traceText: string): Data {
            var entries = traceText.split('\n\n').filter(x => x)
                                   .map(ln => JSON.parse(ln));
            return fromEntries(entries);
        }

        export function fromEntries(entries: any[]): Data {
            var nodes = [], statuses = [], trail = [];
            for (let e of entries) {
                if (NODE_TAGS.includes(e.tag)) nodes.push(e);
                else if (e.tag === DERIVATION_TRAIL_TAG) trail.push(e);
                else if (e.status) statuses.push(e);
            }
            return {nodes, statuses, trail};
        }

        export function parentId(id: NodeId) {
            return id.slice(1);
        }

        export function envOfGoal(goal: GoalEntry) {
            var d: Environment = new Map;
            function intro(vs: [string, string][], of: string) {
                for (let [type, name] of vs) d.set(name, {type, of});
            }
            intro(goal.programVars, 'programVars');
            intro(goal.existentials, 'existentials');
            intro(goal.ghosts, 'ghosts');
            return d;
        }

    }

    // =========
    // View Part
    // =========
    export namespace View {
        
        export type PaneProps = {docs: {[id: string]: {trace: Props}}};

        export type Props = {root: View.Node};

        export type Node = {
            value: Data.NodeEntry
            children: Node[]
            numDescendants: number
            status?: Data.GoalStatusEntry
            derivation?: Data.DerivationTrailEntry
            focus: boolean
            expanded: boolean
        };

        export type ActionEvent = {
            id?: string /* document id */
            type: "expand" | "collapse" | "expandAll" | "menu"
                | "copyNodeId" | "copyGoalId" | "copyGoal",
            target: Node
            $event: MouseEvent
        };

        const OPERATORS = new Map([
            [':->', {pp: "↦"}], ['==', {pp: "="}], ['**', {pp: '∗'}], ['&&', {pp: "∧"}],
            ['not', {pp: "¬"}], ['=i', {pp: "=ᵢ"}], ['++', {pp: '∪'}]]);

        export function tokenize(pp: string, env: Data.Environment) {
            return pp.split(/(\s+|[(){}[\],])/).map(s => {
                var v = env.get(s), op = OPERATORS.get(s), mo: RegExpMatchArray;
                if (v)
                    return {kind: 'var', text: s, pp: pprintIdentifier(s), ...v};
                else if (op)
                    return {kind: 'op', text: s, ...op};
                else if (s.match(/^\s+$/))
                    return {kind: 'whitespace', text: s};
                else if (s.match(/^[(){}[\]]$/))
                    return {kind: 'brace', text: s};
                else if (s === '<0>')
                    return {kind: 'null-cardinality', text: '<??>'}
                else if (mo = s.match(/^<(\w+)>$/))
                    return {kind: 'cardinality', text: s, pp: pprintIdentifier(mo[1])};
                else if (s != '')
                    return {kind: 'unknown', text: s};
            })
            .filter(x => x);
        }

        export function pprintIdentifier(v: string) {
            return v.replace('_alpha_', 'α');
        }
        
    }

}

import Data = ProofTrace.Data;
import View = ProofTrace.View;


abstract class KeyedMap<K, V, K0> {
    _map: Map<K0, V> = new Map();
    abstract key(k: K): K0;
    set(k: K, v: V) {
        this._map.set(this.key(k), v);
    }
    get(k: K) {
        return this._map.get(this.key(k));
    }
}

class JSONMap<K, V> extends KeyedMap<K, V, string> {
    key(k: K) { return JSON.stringify(k); }
}



export { ProofTrace }
