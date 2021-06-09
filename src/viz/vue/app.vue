<template>
    <div class="document-area">
        <app-benchmark-list/>
        <proof-trace-pane ref="proofTrace"/>
    </div>
</template>

<script>
import AppBenchmarkList from './app-benchmark-list.vue';
import ProofTracePane from './proof-trace-pane.vue';

export default {
    components: { ProofTracePane, AppBenchmarkList }
}
</script>