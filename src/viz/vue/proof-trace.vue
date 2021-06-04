<template>
    <div class="proof-trace" :class="[statusClass, root && root.children && root.children.length == 0 ? 'no-children' : 'has-children']">
        <template v-if="root">
            <proof-trace-node ref="nroot" :value="root.value"
                                :status="root.status" :derivation="root.derivation"
                                :num-descendants="root.numDescendants"
                                @action="nodeAction"/>
            <div class="proof-trace-expand-all" :class="{root: root.value.id.length == 0}">
                <span @click="expandAll">++</span>
            </div>
            <div class="subtrees" ref="subtrees" v-if="root.expanded">
                <template v-for="child in root.children">
                    <proof-trace :key="child.value.id.toString()"
                                 :root="child" @action="action"/>
                </template>
            </div>
        </template>
    </div>  
</template>

<script>
import ProofTraceNode from './proof-trace-node.vue';


export default {
    name: 'proof-trace',
    props: ['root'],
    data: () => ({statusClass: undefined}),
    mounted() {
        this.$watch('root.expanded', () => {
            requestAnimationFrame(() => {
                if (this.root.focus && this.$refs.subtrees)
                    this.focusElement(this.$refs.subtrees);
            });
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
            var box = el.getBoundingClientRect(), clrse = 50,
                viewport = window.visualViewport,
                v = (box.bottom + clrse) - viewport.height,
                hl = box.left - clrse - viewport.width * 0.33,
                hr = (box.right + clrse) - viewport.width,
                h = Math.min(hl, hr);
            window.scrollBy({left: Math.max(h, 0), top: Math.max(v, 0), behavior: 'smooth'});
        }
    },
    components: { ProofTraceNode }
}
</script>
