<template>
    <div class="app--ide">
        <div class="app--ide--split-area">
            <benchmark-list-pane :selected="activeBenchmark && activeBenchmark.path" ref="benchmarks"/>
        </div>
        <div class="app--ide--split-area">
            <editor-pane ref="editors" @change="$emit('editor:change', $event)"/>
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
    data: () => ({
        sizes: {benchmarks: 10, editors: 45, proofTrace: 45},
        activeBenchmark: undefined
    }),
    mounted() {
        this.makeResizable(this.$el);
    },
    methods: {
        makeResizable($el) {
            this.split = Split($el.children, {
                sizes: [10, 25, 65],
                snapOffset: 0,
                gutterSize: 3
            });
        }
    },
    components: { ProofTracePane, BenchmarkListPane, EditorPane }
}
</script>