<template>
    <div class="app--ide">
        <div class="app--ide--split-area">
            <benchmark-list-pane ref="benchmarks"/>
        </div>
        <div class="app--ide--split-area">
            <editor-pane ref="editors"/>
        </div>
        <div class="app--ide--split-area">
            <proof-trace-pane ref="proofTrace"/>
        </div>
    </div>
</template>

<style>
.app--ide {
    display: flex;
}
</style>

<script>
import BenchmarkListPane from './benchmark-list-pane.vue';
import EditorPane from './editor-pane.vue';
import ProofTracePane from './proof-trace-pane.vue';

import Split from 'split.js';


export default {
    data: () => ({sizes: {benchmarks: 10, editors: 45, proofTrace: 45}}),
    mounted() {
        this.makeResizable(this.$el);
    },
    methods: {
        makeResizable($el) {
            this.split = Split($el.children, {
                sizes: [10, 45, 45],
                snapOffset: 0,
                gutterSize: 3
            });
        }
    },
    components: { ProofTracePane, BenchmarkListPane, EditorPane }
}
</script>