<template>
    <div class="proof-trace" :class="[statusClass, root && root.children && root.children.length == 0 ? 'no-children' : 'has-children']">
        <template v-if="root">
            <proof-trace-node ref="nroot" :value="root.value"
                                :status="root.status" :derivation="root.derivation"
                                :num-descendants="root.numDescendants"
                                :highlight="getHigh(root.value.id)"
                                @action="nodeAction"/>
            <div class="proof-trace-expand-all" :class="{root: root.value.id.length == 0}">
                <span @click="expandAll">++</span>
            </div>
            <div class="subtrees" ref="subtrees" v-if="root.expanded">
                <template v-for="child in root.children">
                    <proof-trace :key="child.value.id.toString()"
                                 :root="child" :highlight="highlight"
                                 @action="action"/>
                </template>
            </div>
        </template>
    </div>  
</template>

<script>
import _ from 'lodash';
import arreq from 'array-equal';

import ProofTraceNode from './proof-trace-node.vue';


const COALESCE_INTERVAL = 150; /* ms; for exposeq */

var exposeq = { /** @oops this is global */
    boxes: [],
    push(box) { this.boxes.push(box); return this.union(); },
    debounceFlush: _.debounce(() => exposeq.boxes = [], COALESCE_INTERVAL),
    union() {
        var bx = this.boxes;
        var left = Math.min(...bx.map(b => b.left)), right = Math.max(...bx.map(b => b.right)),
            top = Math.min(...bx.map(b => b.top)), bottom = Math.max(...bx.map(b => b.bottom));
        return DOMRect.fromRect({x: left, y: top, width: right - left, height: bottom - top});
    }
};


export default {
    name: 'proof-trace',
    props: ['root', 'highlight'],
    data: () => ({statusClass: undefined}),
    mounted() {
        this.$watch('root.expanded', () => {
            if (this.root?.focus && this.$refs.subtrees)
                requestAnimationFrame(() =>
                    this.focusElement(this.$refs.subtrees));
        });
        if (this.$refs.nroot)
            this.statusClass = this.$refs.nroot.statusClass;
    },
    methods: {
        action(ev) { this.$emit('action', ev); },
        nodeAction(ev) {
            if (ev.type == 'expand/collapse') {
                this.root.expanded = !this.root.expanded;
                ev.type = this.root.expanded ? 'expand' : 'collapse';
            }
            this.action({...ev, target: this.root});
        },
        expandAll() { this.action({type: 'expandAll', target: this.root})},
        focusElement(el) {
            var pane = el.closest('.ide-pane') || document.body,
                box = exposeq.push(el.getBoundingClientRect()), clrse = 50,
                viewport = pane.getBoundingClientRect(), //window.visualViewport,
                v = (box.bottom - viewport.top + clrse) - viewport.height,
                hl = box.left - viewport.left - clrse /*- viewport.width * 0.33*/,
                hr = (box.right - viewport.left + clrse) - viewport.width,
                h = Math.min(hl, hr);
            pane.scrollBy({left: Math.max(h, 0), top: Math.max(v, 0), behavior: 'smooth'});
            exposeq.debounceFlush();
        },
        getHigh(id) {
            return Object.entries(this.highlight || {})
                .map(([k, v]) => v?.some(x => arreq(x, id)) ? k : undefined)
                .filter(x => x);
        }
    },
    components: { ProofTraceNode }
}
</script>
